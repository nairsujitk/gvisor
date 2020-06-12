// Copyright 2018 The gVisor Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package state

import (
	"bytes"
	"context"
	"encoding/gob"
	"fmt"
	"math"
	"reflect"
	"testing"

	"gvisor.dev/gvisor/pkg/state/wire"
)

// TestCase is used to define a single success/failure testcase of
// serialization of a set of objects.
type TestCase struct {
	// Name is the name of the test case.
	Name string

	// Objects is the list of values to serialize.
	Objects []interface{}

	// Fail is whether the test case is supposed to fail or not.
	Fail bool
}

// runTest runs all testcases.
func runTest(t *testing.T, tests []TestCase) {
	for _, test := range tests {
		for i, root := range test.Objects {
			t.Run(fmt.Sprintf("%s.%d", test.Name, i), func(t *testing.T) {

				// Save the passed object.
				saveBuffer := &bytes.Buffer{}
				saveObjectPtr := reflect.New(reflect.TypeOf(root))
				saveObjectPtr.Elem().Set(reflect.ValueOf(root))
				if _, err := Save(context.Background(), saveBuffer, saveObjectPtr.Interface()); err != nil {
					if test.Fail {
						// Save failed, but this case was expected to fail.
						return
					}
					t.Fatalf("Save failed unexpectedly: %v", err)
				}

				// Dump the serialized proto to aid with debugging.
				var ppBuf bytes.Buffer
				t.Logf("Raw state:\n%v", saveBuffer.Bytes())
				PrettyPrint(&ppBuf, bytes.NewReader(saveBuffer.Bytes()), false)
				t.Logf("Encoded state:\n%s", ppBuf.String())

				// Load a new copy of the object.
				loadObjectPtr := reflect.New(reflect.TypeOf(root))
				if _, err := Load(context.Background(), bytes.NewReader(saveBuffer.Bytes()), loadObjectPtr.Interface()); err != nil {
					if test.Fail {
						// Load failed, but this case was expected to fail.
						return
					}
					t.Fatalf("Load failed unexpectedly: %v", err)
				}

				// Compare the values.
				loadedValue := loadObjectPtr.Elem().Interface()
				if eq := reflect.DeepEqual(root, loadedValue); !eq {
					if test.Fail {
						// Objects are different, but we expect this case to fail.
						return
					}
					t.Fatalf("Objects differ:\n\toriginal: %#v\n\tloaded:   %#v\n", root, loadedValue)
				}

				// Everything went okay. Is that good?
				if test.Fail {
					t.Fatalf("This test was expected to fail, but didn't.")
				}
			})
		}
	}
}

// dumbStruct is a struct which does not implement the loader/saver interface.
// We expect that serialization of this struct will fail.
type dumbStruct struct {
	A int
	B int
}

// smartStruct is a struct which does implement the loader/saver interface.
// We expect that serialization of this struct will succeed.
type smartStruct struct {
	A int
	B int
}

func (*smartStruct) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "smartStruct",
		Fields: []string{"A", "B"},
	}
}

func (s *smartStruct) StateSave(m Sink) {
	m.Save(&s.A)
	m.Save(&s.B)
}

func (s *smartStruct) StateLoad(m Source) {
	m.Load(&s.A)
	m.Load(&s.B)
}

// valueLoadStruct uses a value load.
type valueLoadStruct struct {
	v int
}

func (*valueLoadStruct) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "valueStruct",
		Fields: []string{"v"},
	}
}

func (v *valueLoadStruct) StateSave(m Sink) {
	m.SaveValue(v.v)
}

func (v *valueLoadStruct) StateLoad(m Source) {
	m.LoadValue(new(int), func(value interface{}) {
		v.v = value.(int)
	})
}

// afterLoadStruct has an AfterLoad function.
type afterLoadStruct struct {
	v int
}

func (*afterLoadStruct) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name: "afterLoadStruct",
	}
}

func (a *afterLoadStruct) StateSave(m Sink) {
}

func (a *afterLoadStruct) StateLoad(m Source) {
	m.AfterLoad(func() {
		a.v++
	})
}

// genericContainer is a generic dispatcher.
type genericContainer struct {
	v interface{}
}

func (*genericContainer) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "genericContainer",
		Fields: []string{"v"},
	}
}

func (g *genericContainer) StateSave(m Sink) {
	m.Save(&g.v)
}

func (g *genericContainer) StateLoad(m Source) {
	m.Load(&g.v)
}

// sliceContainer is a generic slice.
type sliceContainer struct {
	v []interface{}
}

func (*sliceContainer) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "sliceContainer",
		Fields: []string{"v"},
	}
}

func (s *sliceContainer) StateSave(m Sink) {
	m.Save(&s.v)
}

func (s *sliceContainer) StateLoad(m Source) {
	m.Load(&s.v)
}

// mapContainer is a generic map.
type mapContainer struct {
	v map[int]interface{}
}

func (*mapContainer) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "mapContainer",
		Fields: []string{"v"},
	}
}

func (mc *mapContainer) StateSave(m Sink) {
	m.Save(&mc.v)
}

func (mc *mapContainer) StateLoad(m Source) {
	// Some of the test cases below assume legacy behavior wherein maps
	// will automatically inherit dependencies.
	m.LoadWait(&mc.v)
}

type mapPtrContainer struct {
	v *map[int]interface{}
}

func (*mapPtrContainer) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "mapPtrContainer",
		Fields: []string{"v"},
	}
}

func (mc *mapPtrContainer) StateSave(m Sink) {
	m.Save(&mc.v)
}

func (mc *mapPtrContainer) StateLoad(m Source) {
	// Some of the test cases below assume legacy behavior wherein maps
	// will automatically inherit dependencies.
	m.LoadWait(&mc.v)
}

// dumbMap is a map which does not implement the loader/saver interface.
// Serialization of this map will default to the standard encode/decode logic.
type dumbMap map[string]int

// pointerStruct contains various pointers, shared and non-shared, and pointers
// to pointers. We expect that serialization will respect the structure.
type pointerStruct struct {
	A *int
	B *int
	C *int
	D *int

	AA **int
	BB **int
}

func (*pointerStruct) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "pointerStruct",
		Fields: []string{"A", "B", "C", "D", "AA", "BB"},
	}
}

func (p *pointerStruct) StateSave(m Sink) {
	m.Save(&p.A)
	m.Save(&p.B)
	m.Save(&p.C)
	m.Save(&p.D)
	m.Save(&p.AA)
	m.Save(&p.BB)
}

func (p *pointerStruct) StateLoad(m Source) {
	m.Load(&p.A)
	m.Load(&p.B)
	m.Load(&p.C)
	m.Load(&p.D)
	m.Load(&p.AA)
	m.Load(&p.BB)
}

type testInterface interface {
	Foo()
}

type testImpl struct {
}

func (t *testImpl) Foo() {
}

func (*testImpl) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name: "testImpl",
	}
}

func (t *testImpl) StateSave(m Sink) {
}

func (t *testImpl) StateLoad(m Source) {
}

type testI struct {
	I testInterface
}

func (*testI) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "testI",
		Fields: []string{"I"},
	}
}

func (t *testI) StateSave(m Sink) {
	m.Save(&t.I)
}

func (t *testI) StateLoad(m Source) {
	m.Load(&t.I)
}

// cycleStruct is used to implement basic cycles.
type cycleStruct struct {
	c *cycleStruct
}

func (*cycleStruct) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "cycleStruct",
		Fields: []string{"c"},
	}
}

func (c *cycleStruct) StateSave(m Sink) {
	m.Save(&c.c)
}

func (c *cycleStruct) StateLoad(m Source) {
	m.Load(&c.c)
}

// badCycleStruct actually has deadlocking dependencies.
//
// This should pass if b.b = {nil|b} and fail otherwise.
type badCycleStruct struct {
	b *badCycleStruct
}

func (*badCycleStruct) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "badCycleStruct",
		Fields: []string{"b"},
	}
}

func (b *badCycleStruct) StateSave(m Sink) {
	m.Save(&b.b)
}

func (b *badCycleStruct) StateLoad(m Source) {
	m.LoadWait(&b.b)
	m.AfterLoad(func() {
		// This is not executable, since AfterLoad requires that the
		// object and all dependencies are complete. This should cause
		// a deadlock error during load.
	})
}

// emptyStructPointer points to an empty struct.
type emptyStructPointer struct {
	nothing *struct{}
}

func (*emptyStructPointer) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "emptyStructPointer",
		Fields: []string{"nothing"},
	}
}

func (e *emptyStructPointer) StateSave(m Sink) {
	m.Save(&e.nothing)
}

func (e *emptyStructPointer) StateLoad(m Source) {
	m.Load(&e.nothing)
}

// truncateInteger truncates an integer.
type truncateInteger struct {
	v  int64
	v2 int32
}

func (*truncateInteger) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "truncateInteger",
		Fields: []string{"v"},
	}
}

func (t *truncateInteger) StateSave(m Sink) {
	t.v2 = int32(t.v)
	m.Save(&t.v)
}

func (t *truncateInteger) StateLoad(m Source) {
	m.Load(&t.v2)
	t.v = int64(t.v2)
}

// truncateUnsignedInteger truncates an unsigned integer.
type truncateUnsignedInteger struct {
	v  uint64
	v2 uint32
}

func (*truncateUnsignedInteger) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "truncateUnsignedInteger",
		Fields: []string{"v"},
	}
}

func (t *truncateUnsignedInteger) StateSave(m Sink) {
	t.v2 = uint32(t.v)
	m.Save(&t.v)
}

func (t *truncateUnsignedInteger) StateLoad(m Source) {
	m.Load(&t.v2)
	t.v = uint64(t.v2)
}

// truncateFloat truncates a floating point number.
type truncateFloat struct {
	v  float64
	v2 float32
}

func (*truncateFloat) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "truncateFloat",
		Fields: []string{"v"},
	}
}

func (t *truncateFloat) StateSave(m Sink) {
	t.v2 = float32(t.v)
	m.Save(&t.v)
}

func (t *truncateFloat) StateLoad(m Source) {
	m.Load(&t.v2)
	t.v = float64(t.v2)
}

type outer struct {
	a  int64
	cn *container
}

func (*outer) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "outer",
		Fields: []string{"a", "cn"},
	}
}

func (o *outer) StateSave(m Sink) {
	m.Save(&o.a)
	m.Save(&o.cn)
}

func (o *outer) StateLoad(m Source) {
	m.Load(&o.a)
	m.LoadValue(new(*container), func(x interface{}) {
		o.cn = x.(*container)
	})
}

type container struct {
	n    uint64
	elem *inner
}

func (c *container) init(o *outer, i *inner) {
	c.elem = i
	o.cn = c
}

func (*container) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "container",
		Fields: []string{"n", "elem"},
	}
}

func (c *container) StateSave(m Sink) {
	m.Save(&c.n)
	m.Save(&c.elem)
}

func (c *container) StateLoad(m Source) {
	m.Load(&c.n)
	m.Load(&c.elem)
}

type inner struct {
	c    container
	x, y uint64
}

func (*inner) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "inner",
		Fields: []string{"c", "x", "y"},
	}
}

func (i *inner) StateSave(m Sink) {
	m.Save(&i.c)
	m.Save(&i.x)
	m.Save(&i.y)
}

func (i *inner) StateLoad(m Source) {
	m.Load(&i.c)
	m.Load(&i.x)
	m.Load(&i.y)
}

type system struct {
	o *outer
	i *inner
}

func (*system) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "system",
		Fields: []string{"o", "i"},
	}
}

func (s *system) StateSave(m Sink) {
	m.Save(&s.o)
	m.Save(&s.i)
}

func (s *system) StateLoad(m Source) {
	m.Load(&s.o)
	m.Load(&s.i)
}

func TestTypes(t *testing.T) {
	// x and y are basic integers, while xp points to x.
	x := 1
	y := 2
	xp := &x

	// cs is a single object cycle.
	cs := cycleStruct{nil}
	cs.c = &cs

	// cs1 and cs2 are in a two object cycle.
	cs1 := cycleStruct{nil}
	cs2 := cycleStruct{nil}
	cs1.c = &cs2
	cs2.c = &cs1

	// bs is a single object cycle.
	bs := badCycleStruct{nil}
	bs.b = &bs

	// bs2 and bs2 are in a deadlocking cycle.
	bs1 := badCycleStruct{nil}
	bs2 := badCycleStruct{nil}
	bs1.b = &bs2
	bs2.b = &bs1

	// regular nils.
	var (
		nilmap   dumbMap
		nilslice []byte
	)

	// embed points to embedded fields.
	embed1 := pointerStruct{}
	embed1.AA = &embed1.A
	embed2 := pointerStruct{}
	embed2.BB = &embed2.B

	// es1 contains two structs pointing to the same empty struct.
	es := emptyStructPointer{new(struct{})}
	es1 := []emptyStructPointer{es, es}

	o := outer{
		a: 10,
	}
	i := inner{
		x: 20,
		y: 30,
	}
	i.c.init(&o, &i)

	s := system{
		o: &o,
		i: &i,
	}

	tests := []TestCase{
		{
			Name: "interlocking field pointer",
			Objects: []interface{}{
				s,
			},
		},
		{
			Name: "bool",
			Objects: []interface{}{
				true,
				false,
			},
		},
		{
			Name: "integers",
			Objects: []interface{}{
				int(0),
				int(1),
				int(-1),
				int8(0),
				int8(1),
				int8(-1),
				int16(0),
				int16(1),
				int16(-1),
				int32(0),
				int32(1),
				int32(-1),
				int64(0),
				int64(1),
				int64(-1),
			},
		},
		{
			Name: "unsigned integers",
			Objects: []interface{}{
				uint(0),
				uint(1),
				uint8(0),
				uint8(1),
				uint16(0),
				uint16(1),
				uint32(1),
				uint64(0),
				uint64(1),
			},
		},
		{
			Name: "strings",
			Objects: []interface{}{
				"",
				"foo",
				"bar",
				"\xa0",
			},
		},
		{
			Name: "slices",
			Objects: []interface{}{
				[]int{-1, 0, 1},
				[]*int{&x, &x, &x},
				[]int{1, 2, 3}[0:1],
				[]int{1, 2, 3}[1:2],
				make([]byte, 32),
				make([]byte, 32)[:16],
				make([]byte, 32)[:16:20],
				nilslice,
			},
		},
		{
			Name: "arrays",
			Objects: []interface{}{
				&[5]bool{false, true, false, true},
				&[5]uint8{0, 1, 2, 3},
				&[5]byte{0, 1, 2, 3},
				&[5]uint16{0, 1, 2, 3},
				&[5]uint{0, 1, 2, 3},
				&[5]uint32{0, 1, 2, 3},
				&[5]uint64{0, 1, 2, 3},
				&[5]uintptr{0, 1, 2, 3},
				&[5]int8{0, -1, -2, -3},
				&[5]int16{0, -1, -2, -3},
				&[5]int32{0, -1, -2, -3},
				&[5]int64{0, -1, -2, -3},
				&[5]float32{0, 1.1, 2.2, 3.3},
				&[5]float64{0, 1.1, 2.2, 3.3},
			},
		},
		{
			Name: "pointers",
			Objects: []interface{}{
				&pointerStruct{A: &x, B: &x, C: &y, D: &y, AA: &xp, BB: &xp},
				&pointerStruct{},
			},
		},
		{
			Name: "empty struct",
			Objects: []interface{}{
				struct{}{},
			},
		},
		{
			Name: "unenlightened structs",
			Objects: []interface{}{
				&dumbStruct{A: 1, B: 2},
			},
			Fail: true,
		},
		{
			Name: "enlightened structs",
			Objects: []interface{}{
				&smartStruct{A: 1, B: 2},
			},
		},
		{
			Name: "load-hooks",
			Objects: []interface{}{
				&afterLoadStruct{v: 1},
				&valueLoadStruct{v: 1},
				&genericContainer{v: &afterLoadStruct{v: 1}},
				&genericContainer{v: &valueLoadStruct{v: 1}},
				&sliceContainer{v: []interface{}{&afterLoadStruct{v: 1}}},
				&sliceContainer{v: []interface{}{&valueLoadStruct{v: 1}}},
				&mapContainer{v: map[int]interface{}{0: &afterLoadStruct{v: 1}}},
				&mapContainer{v: map[int]interface{}{0: &valueLoadStruct{v: 1}}},
			},
		},
		{
			Name: "maps",
			Objects: []interface{}{
				dumbMap{"a": -1, "b": 0, "c": 1},
				map[smartStruct]int{{}: 0, {A: 1}: 1},
				nilmap,
				&mapContainer{v: map[int]interface{}{0: &smartStruct{A: 1}}},
			},
		},
		{
			Name: "map ptr",
			Objects: []interface{}{
				&mapPtrContainer{v: &map[int]interface{}{0: &smartStruct{A: 1}}},
			},
			Fail: true,
		},
		{
			Name: "interfaces",
			Objects: []interface{}{
				&testI{&testImpl{}},
				&testI{nil},
				&testI{(*testImpl)(nil)},
			},
		},
		{
			Name: "unregistered-interfaces",
			Objects: []interface{}{
				&genericContainer{v: afterLoadStruct{v: 1}},
				&genericContainer{v: valueLoadStruct{v: 1}},
				&sliceContainer{v: []interface{}{afterLoadStruct{v: 1}}},
				&sliceContainer{v: []interface{}{valueLoadStruct{v: 1}}},
				&mapContainer{v: map[int]interface{}{0: afterLoadStruct{v: 1}}},
				&mapContainer{v: map[int]interface{}{0: valueLoadStruct{v: 1}}},
			},
			Fail: true,
		},
		{
			Name: "cycles",
			Objects: []interface{}{
				&cs,
				&cs1,
				&cycleStruct{&cs1},
				&cycleStruct{&cs},
				&badCycleStruct{nil},
				&bs,
			},
		},
		{
			Name: "deadlock",
			Objects: []interface{}{
				&bs1,
			},
			Fail: true,
		},
		{
			Name: "embed",
			Objects: []interface{}{
				&embed1,
				&embed2,
			},
		},
		{
			Name: "empty structs",
			Objects: []interface{}{
				new(struct{}),
				es,
				es1,
			},
		},
		{
			Name: "truncated okay",
			Objects: []interface{}{
				&truncateInteger{v: 1},
				&truncateUnsignedInteger{v: 1},
				&truncateFloat{v: 1.0},
			},
		},
		{
			Name: "truncated bad",
			Objects: []interface{}{
				&truncateInteger{v: math.MaxInt32 + 1},
				&truncateUnsignedInteger{v: math.MaxUint32 + 1},
				&truncateFloat{v: math.MaxFloat32 * 2},
			},
			Fail: true,
		},
	}

	runTest(t, tests)
}

// benchStruct is used for benchmarking.
type benchStruct struct {
	B *benchStruct // Must be exported for gob.
}

func (*benchStruct) StateTypeInfo() TypeInfo {
	return TypeInfo{
		Name:   "benchStruct",
		Fields: []string{"B"},
	}
}

func (b *benchStruct) StateSave(m Sink) {
	m.Save(&b.B)
}

func (b *benchStruct) StateLoad(m Source) {
	m.LoadWait(&b.B)
	m.AfterLoad(b.afterLoad)
}

func (b *benchStruct) afterLoad() {
	// Do nothing, just force scheduling.
}

// buildPtrObject builds a benchmark object.
func buildPtrObject(n int) interface{} {
	b := new(benchStruct)
	for i := 0; i < n; i++ {
		b = &benchStruct{B: b}
	}
	return b
}

// buildMapObject builds a benchmark object.
func buildMapObject(n int) interface{} {
	b := new(benchStruct)
	m := make(map[int]*benchStruct)
	for i := 0; i < n; i++ {
		m[i] = b
	}
	return &m
}

// buildSliceObject builds a benchmark object.
func buildSliceObject(n int) interface{} {
	b := new(benchStruct)
	s := make([]*benchStruct, 0, n)
	for i := 0; i < n; i++ {
		s = append(s, b)
	}
	return &s
}

var allObjects = map[string]struct {
	New func(int) interface{}
}{
	"ptr": {
		New: buildPtrObject,
	},
	"map": {
		New: buildMapObject,
	},
	"slice": {
		New: buildSliceObject,
	},
}

func buildObjects(n int, fn func(int) interface{}) (iters int, v interface{}) {
	// maxSize is the maximum size of an individual object below. For an N
	// larger than this, we start to return multiple objects.
	const maxSize = 1024
	if n <= maxSize {
		return 1, fn(n)
	}
	iters = (n + maxSize - 1) / maxSize
	return iters, fn(maxSize)
}

// gobSave is a version of save using gob (no stats available).
func gobSave(_ context.Context, w wire.Writer, v interface{}) (_ Stats, err error) {
	enc := gob.NewEncoder(w)
	err = enc.Encode(v)
	return
}

// gobLoad is a version of load using gob (no stats available).
func gobLoad(_ context.Context, r wire.Reader, v interface{}) (_ Stats, err error) {
	dec := gob.NewDecoder(r)
	err = dec.Decode(v)
	return
}

var allAlgos = map[string]struct {
	Save   func(context.Context, wire.Writer, interface{}) (Stats, error)
	Load   func(context.Context, wire.Reader, interface{}) (Stats, error)
	MaxPtr int
}{
	"state": {
		Save: Save,
		Load: Load,
	},
	"gob": {
		Save: gobSave,
		Load: gobLoad,
	},
}

// discard is an implementation of wire.Writer.
type discard struct{}

// Write implements wire.Writer.Write.
func (discard) Write(p []byte) (int, error) { return len(p), nil }

// WriteByte implements wire.Writer.WriteByte.
func (discard) WriteByte(byte) error { return nil }

func BenchmarkEncoding(b *testing.B) {
	for objName, objInfo := range allObjects {
		for algoName, algoInfo := range allAlgos {
			b.Run(fmt.Sprintf("%s/%s", objName, algoName), func(b *testing.B) {
				b.StopTimer()
				n, v := buildObjects(b.N, objInfo.New)
				b.ReportAllocs()
				b.StartTimer()
				for i := 0; i < n; i++ {
					if _, err := algoInfo.Save(context.Background(), discard{}, v); err != nil {
						b.Errorf("save failed: %v", err)
					}
				}
				b.StopTimer()
			})
		}
	}
}

func BenchmarkDecoding(b *testing.B) {
	for objName, objInfo := range allObjects {
		for algoName, algoInfo := range allAlgos {
			b.Run(fmt.Sprintf("%s/%s", objName, algoName), func(b *testing.B) {
				b.StopTimer()
				n, v := buildObjects(b.N, objInfo.New)
				buf := new(bytes.Buffer)
				if _, err := algoInfo.Save(context.Background(), buf, v); err != nil {
					b.Errorf("save failed: %v", err)
				}
				b.ReportAllocs()
				b.StartTimer()
				var r bytes.Reader
				for i := 0; i < n; i++ {
					r.Reset(buf.Bytes())
					if _, err := algoInfo.Load(context.Background(), &r, v); err != nil {
						b.Errorf("load failed: %v", err)
					}
				}
				b.StopTimer()
			})
		}
	}
}

func init() {
	allObjects := []Type{
		(*system)(nil),
		(*outer)(nil),
		(*container)(nil),
		(*inner)(nil),
		(*smartStruct)(nil),
		(*afterLoadStruct)(nil),
		(*valueLoadStruct)(nil),
		(*genericContainer)(nil),
		(*sliceContainer)(nil),
		(*mapContainer)(nil),
		(*mapPtrContainer)(nil),
		(*pointerStruct)(nil),
		(*testImpl)(nil),
		(*testI)(nil),
		(*cycleStruct)(nil),
		(*badCycleStruct)(nil),
		(*emptyStructPointer)(nil),
		(*truncateInteger)(nil),
		(*truncateUnsignedInteger)(nil),
		(*truncateFloat)(nil),
		(*benchStruct)(nil),
	}
	for _, ptr := range allObjects {
		Register(ptr)
		gob.Register(ptr)
	}
}
