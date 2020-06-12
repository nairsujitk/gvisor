// Copyright 2020 The gVisor Authors.
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

// Package wire contains a few basic types that can be composed to serialize
// graph information for the state package. This package defines the wire
// protocol.
//
// Note that these types are careful about how they implement the relevant
// interfaces (either value receiver or pointer receiver), so that native-sized
// types, such as integers and simple pointers, can fit inside the interface
// object.
//
// This package also uses panic as control flow, so called should be careful to
// wrap calls in appropriate handlers.
package wire

import (
	"encoding/binary"
	"fmt"
	"io"

	"gvisor.dev/gvisor/pkg/gohacks"
)

// Reader is the required reader interface.
type Reader interface {
	io.Reader
	ReadByte() (byte, error)
}

// Writer is the required writer interface.
type Writer interface {
	io.Writer
	WriteByte(byte) error
}

// readFull is a utility. The equivalent is not needed for Write, but the API
// contract dictates that it must always complete all bytes given or return an
// error.
func readFull(r io.Reader, p []byte) {
	for done := 0; done < len(p); {
		n, err := r.Read(p[done:])
		done += n
		if n == 0 && err != nil {
			panic(err)
		}
	}
}

// Object is a generic object.
type Object interface {
	// Save saves the given object.
	//
	// Panic is used for error control flow.
	Save(Writer)

	// load runs the loader for the type.
	//
	// Panic is used for error control flow.
	load(Reader) Object
}

// Bool is a boolean.
type Bool bool

// LoadBool loads an object of type Bool.
func LoadBool(r Reader) Bool {
	b := LoadUint(r)
	return Bool(b == 1)
}

// load implements Object.load.
func (Bool) load(r Reader) Object { return LoadBool(r) }

// Save implements Object.Save.
func (b Bool) Save(w Writer) {
	var v Uint
	if b {
		v = 1
	} else {
		v = 0
	}
	v.Save(w)
}

// Int is a signed integer.
type Int int64

// LoadInt loads an object of type Int.
func LoadInt(r Reader) Int {
	u := LoadUint(r)
	x := Int(u >> 1)
	if u&1 != 0 {
		x = ^x
	}
	return x
}

// load implements Object.load.
func (Int) load(r Reader) Object { return LoadInt(r) }

// Save implements Object.Save.
func (i Int) Save(w Writer) {
	u := Uint(i) << 1
	if i < 0 {
		u = ^u
	}
	u.Save(w)
}

// Uint is an unsigned integer.
type Uint uint64

// LoadUint loads an object of type Uint.
func LoadUint(r Reader) Uint {
	var (
		u Uint
		s uint
	)
	for i := 0; i <= 9; i++ {
		b, err := r.ReadByte()
		if err != nil {
			panic(err)
		}
		if b < 0x80 {
			if i == 9 && b > 1 {
				panic("overflow")
			}
			u |= Uint(b) << s
			return u
		}
		u |= Uint(b&0x7f) << s
		s += 7
	}
	return u
}

// load implements Object.load.
func (Uint) load(r Reader) Object { return LoadUint(r) }

// Save implements Object.Save.
func (u Uint) Save(w Writer) {
	for u >= 0x80 {
		if err := w.WriteByte(byte(u) | 0x80); err != nil {
			panic(err)
		}
		u >>= 7
	}
	if err := w.WriteByte(byte(u)); err != nil {
		panic(err)
	}
}

// Float is a floating point number.
type Float float64

// LoadFloat loads an object of type Float.
func LoadFloat(r Reader) Float {
	var f float64
	if err := binary.Read(r, binary.BigEndian, &f); err != nil {
		panic(err)
	}
	return Float(f)
}

// load implements Object.load.
func (Float) load(r Reader) Object {
	return LoadFloat(r)
}

// Save implements Object.Save.
func (f Float) Save(w Writer) {
	if err := binary.Write(w, binary.BigEndian, f); err != nil {
		panic(err)
	}
}

// Complex is a complex number.
type Complex complex128

// LoadComplex loads an object of type Complex.
func LoadComplex(r Reader) *Complex {
	re := LoadFloat(r)
	im := LoadFloat(r)
	c := Complex(complex(float64(re), float64(im)))
	return &c
}

// load implements Object.load.
func (*Complex) load(r Reader) Object { return LoadComplex(r) }

// Save implements Object.Save.
func (c *Complex) Save(w Writer) {
	re := Float(real(*c))
	im := Float(imag(*c))
	re.Save(w)
	im.Save(w)
}

// String is a string.
type String string

// LoadString loads an object of type String.
func LoadString(r Reader) String {
	l := LoadUint(r)
	p := make([]byte, l)
	readFull(r, p)
	s := String(gohacks.StringFromImmutableBytes(p))
	return s
}

// load implements Object.load.
func (*String) load(r Reader) Object {
	s := LoadString(r)
	return &s
}

// Save implements Object.Save.
func (s *String) Save(w Writer) {
	l := Uint(len(*s))
	l.Save(w)
	p := gohacks.ImmutableBytesFromString(string(*s))
	_, err := w.Write(p) // Must write all bytes.
	if err != nil {
		panic(err)
	}
}

// Dot is a kind of reference: one of Index and FieldName.
type Dot interface {
	isDot()
}

// Index is a reference resolution.
type Index uint32

func (Index) isDot() {}

// FieldName is a reference resolution.
type FieldName string

func (*FieldName) isDot() {}

// Ref is a reference to an object.
type Ref struct {
	// Root is the root object.
	Root Uint

	// Dots is the set of traversals required from the Root object above.
	// Note that this will be stored in reverse order for efficiency.
	Dots []Dot
}

// LoadRef loads an object of type Ref (abstract).
func LoadRef(r Reader) Ref {
	// N.B. That this disambiguates between a simple ref (which does not
	// have any components) and a more complex ref (which does not). This
	// is done to save space for pointer encoding, which would otherwise
	// require a type value always.
	v := LoadInt(r)
	if v >= 0 {
		// This is a simple reference.
		return Ref{
			Root: Uint(v),
		}
	}
	l := LoadUint(r)
	dots := make([]Dot, 0, l)
	for i := 0; i < int(l); i++ {
		d := LoadInt(r)
		if d >= 0 {
			dots = append(dots, Index(d))
			continue
		}
		p := make([]byte, -d)
		readFull(r, p)
		fieldName := FieldName(gohacks.StringFromImmutableBytes(p))
		dots = append(dots, &fieldName)
	}
	return Ref{
		Root: Uint(-v),
		Dots: dots,
	}
}

// load implements Object.load.
func (*Ref) load(r Reader) Object {
	ref := LoadRef(r)
	return &ref
}

// Save implements Object.Save.
func (r *Ref) Save(w Writer) {
	// Save as positive.
	v := Int(r.Root)
	if len(r.Dots) == 0 {
		v.Save(w)
		return
	}
	// Save as negative.
	v = -v
	v.Save(w)
	l := Uint(len(r.Dots))
	l.Save(w)
	for _, d := range r.Dots {
		switch x := d.(type) {
		case Index:
			i := Int(x)
			i.Save(w)
		case *FieldName:
			d := Int(-len(*x))
			d.Save(w)
			p := gohacks.ImmutableBytesFromString(string(*x))
			if _, err := w.Write(p); err != nil {
				panic(err)
			}
		default:
			panic("unknown dot implementation")
		}
	}
}

// Nil is a primitive zero value of any type.
type Nil struct{}

// Save implements Object.Save.
func (Nil) Save(w Writer) {}

// LoadNil loads an object of type Nil.
func LoadNil(r Reader) Nil {
	return Nil{}
}

// load implements Object.load.
func (Nil) load(r Reader) Object { return LoadNil(r) }

// Slice is a slice value.
type Slice struct {
	Length   Uint
	Capacity Uint
	Ref      Ref
}

// LoadSlice loads an object of type Slice.
func LoadSlice(r Reader) Slice {
	return Slice{
		Length:   LoadUint(r),
		Capacity: LoadUint(r),
		Ref:      LoadRef(r),
	}
}

// load implements Object.load.
func (*Slice) load(r Reader) Object {
	s := LoadSlice(r)
	return &s
}

// Save implements Object.Save.
func (s *Slice) Save(w Writer) {
	s.Length.Save(w)
	s.Capacity.Save(w)
	s.Ref.Save(w)
}

// Array is an array value.
type Array struct {
	Contents []Object
}

// LoadArray loads an object of type Array.
func LoadArray(r Reader) *Array {
	l := LoadUint(r)
	if l == 0 {
		return &Array{}
	}
	// All the objects here have the same type, so use dynamic dispatch
	// only once. All other objects will automatically take the same type
	// as the first object.
	contents := make([]Object, l)
	v := Load(r)
	contents[0] = v
	for i := 1; i < int(l); i++ {
		contents[i] = v.load(r)
	}
	return &Array{
		Contents: contents,
	}
}

// load implements Object.load.
func (*Array) load(r Reader) Object { return LoadArray(r) }

// Save implements Object.Save.
func (a *Array) Save(w Writer) {
	l := Uint(len(a.Contents))
	l.Save(w)
	if l == 0 {
		return
	}
	// See above.
	Save(w, a.Contents[0])
	for i := 1; i < int(l); i++ {
		a.Contents[i].Save(w)
	}
}

// Map is a map value.
type Map struct {
	Keys   []Object
	Values []Object
}

// LoadMap loads an object of type Map.
func LoadMap(r Reader) Map {
	l := LoadUint(r)
	if l == 0 {
		return Map{}
	}
	// See type dispatch notes in Array.
	keys := make([]Object, l)
	values := make([]Object, l)
	k := Load(r)
	v := Load(r)
	keys[0] = k
	values[0] = v
	for i := 1; i < int(l); i++ {
		keys[i] = k.load(r)
		values[i] = v.load(r)
	}
	return Map{
		Keys:   keys,
		Values: values,
	}
}

// load implements Object.load.
func (*Map) load(r Reader) Object {
	m := LoadMap(r)
	return &m
}

// Save implements Object.Save.
func (m *Map) Save(w Writer) {
	l := Uint(len(m.Keys))
	if int(l) != len(m.Values) {
		panic(fmt.Sprintf("mismatched keys (%d) Aand values (%d)", len(m.Keys), len(m.Values)))
	}
	l.Save(w)
	if l == 0 {
		return
	}
	// See above.
	Save(w, m.Keys[0])
	Save(w, m.Values[0])
	for i := 1; i < int(l); i++ {
		m.Keys[i].Save(w)
		m.Values[i].Save(w)
	}
}

// Interface is an interface value.
type Interface struct {
	TypeID Uint
	Value  Object
}

// LoadInterface loads an object of type Interface.
func LoadInterface(r Reader) Interface {
	return Interface{
		TypeID: LoadUint(r),
		Value:  Load(r),
	}
}

// load implements Object.load.
func (*Interface) load(r Reader) Object {
	i := LoadInterface(r)
	return &i
}

// Save implements Object.Save.
func (i *Interface) Save(w Writer) {
	i.TypeID.Save(w)
	Save(w, i.Value)
}

// Type is type information.
type Type struct {
	Name   String
	Fields []String
}

// LoadType loads an object of type Type.
func LoadType(r Reader) Type {
	name := LoadString(r)
	l := LoadUint(r)
	if l == 0 {
		return Type{
			Name: name,
		}
	}
	fields := make([]String, l)
	for i := 0; i < int(l); i++ {
		fields[i] = LoadString(r)
	}
	return Type{
		Name:   name,
		Fields: fields,
	}
}

// load implements Object.load.
func (*Type) load(r Reader) Object {
	t := LoadType(r)
	return &t
}

// Save implements Object.Save.
func (t *Type) Save(w Writer) {
	t.Name.Save(w)
	l := Uint(len(t.Fields))
	l.Save(w)
	for i := 0; i < int(l); i++ {
		t.Fields[i].Save(w)
	}
}

// multipleObjects is a special type for serializing multiple objects.
type multipleObjects []Object

// loadMultipleObjects loads a series of objects.
func loadMultipleObjects(r Reader) *multipleObjects {
	l := LoadUint(r)
	if l == 0 {
		return nil
	}
	m := make(multipleObjects, l)
	for i := 0; i < int(l); i++ {
		m[i] = Load(r)
	}
	return &m
}

// load implements Object.load.
func (*multipleObjects) load(r Reader) Object {
	return loadMultipleObjects(r)
}

// Save implements Object.Save.
func (m *multipleObjects) Save(w Writer) {
	l := Uint(len(*m))
	l.Save(w)
	for i := 0; i < int(l); i++ {
		Save(w, (*m)[i])
	}
}

// noObjects represents no objects.
type noObjects struct{}

// loadNoObjects loads a sentinel.
func loadNoObjects(r Reader) noObjects { return noObjects{} }

// load implements Object.load.
func (noObjects) load(r Reader) Object {
	return loadNoObjects(r)
}

// Save implements Object.Save.
func (noObjects) Save(w Writer) {}

// Struct is a basic composite value.
type Struct struct {
	TypeID Uint
	fields Object // Optionally noObjects or *multipleObjects.
}

// Add adds a field to the object.
//
// This must be called after Alloc and before Save.
func (s *Struct) Add() *Object {
	if fields, ok := s.fields.(*multipleObjects); ok {
		l := len(*fields)
		if l == cap(*fields) {
			// Insufficient fields allocated.
			panic(fmt.Sprintf("Add called %d times Alloc(%d)", l+1, l))
		}
		(*fields) = append(*fields, nil)
		return &(*fields)[l]
	}
	if s.fields != nil {
		// Alloc may be optionally called; can't call twice.
		panic("Add called inappropriately, wrong Alloc?")
	}
	return &s.fields
}

// Alloc allocates the given number of fields.
//
// This must be called before Add and Save.
//
// Precondition: slots must be positive.
func (s *Struct) Alloc(slots int) {
	switch {
	case slots == 0:
		s.fields = noObjects{}
	case slots == 1:
		return
	case slots > 1:
		fields := make(multipleObjects, 0, slots)
		s.fields = &fields
	default:
		// Violates precondition.
		panic(fmt.Sprintf("Alloc called with negative slots %d?", slots))
	}
}

// Next returns the next field.
//
// Precondition: the Struct must be loaded or Alloc called.
func (s *Struct) Next() (Object, bool) {
	switch x := s.fields.(type) {
	case nil:
		panic("Next called without Alloc?")
	case noObjects:
		return nil, false
	case *multipleObjects:
		v := (*x)[0]
		(*x) = (*x)[1:]
		if len(*x) == 0 {
			// Consumed everything.
			s.fields = noObjects{}
		}
		return v, true
	default:
		v := x
		// Consumed the object.
		s.fields = noObjects{}
		return v, true
	}
}

// LoadStruct loads an object of type Struct.
func LoadStruct(r Reader) Struct {
	return Struct{
		TypeID: LoadUint(r),
		fields: Load(r),
	}
}

// load implements Object.load.
func (*Struct) load(r Reader) Object {
	s := LoadStruct(r)
	return &s
}

// Save implements Object.Save.
//
// Precondition: Alloc must have been called, and the fields all filled in
// appropriately. See Alloc and Add for more details.
func (s *Struct) Save(w Writer) {
	s.TypeID.Save(w)
	Save(w, s.fields)
}

// Object types.
//
// N.B. Be careful about changing the order or introducing new elements in the
// middle here. This is part of the wire format and shouldn't change.
const (
	typeBool Uint = iota
	typeInt
	typeUint
	typeFloat
	typeNil
	typeRef
	typeString
	typeSlice
	typeArray
	typeMap
	typeStruct
	typeNoObjects
	typeMultipleObjects
	typeInterface
	typeType
	typeComplex
)

// Save saves the given object.
//
// N.B. This function will panic on error.
func Save(w Writer, obj Object) {
	switch x := obj.(type) {
	case Bool:
		typeBool.Save(w)
		x.Save(w)
	case Int:
		typeInt.Save(w)
		x.Save(w)
	case Uint:
		typeUint.Save(w)
		x.Save(w)
	case Float:
		typeFloat.Save(w)
		x.Save(w)
	case Nil:
		typeNil.Save(w)
		x.Save(w)
	case *Ref:
		typeRef.Save(w)
		x.Save(w)
	case *String:
		typeString.Save(w)
		x.Save(w)
	case *Slice:
		typeSlice.Save(w)
		x.Save(w)
	case *Array:
		typeArray.Save(w)
		x.Save(w)
	case *Map:
		typeMap.Save(w)
		x.Save(w)
	case *Struct:
		typeStruct.Save(w)
		x.Save(w)
	case noObjects:
		typeNoObjects.Save(w)
		x.Save(w)
	case *multipleObjects:
		typeMultipleObjects.Save(w)
		x.Save(w)
	case *Interface:
		typeInterface.Save(w)
		x.Save(w)
	case *Type:
		typeType.Save(w)
		x.Save(w)
	case *Complex:
		typeComplex.Save(w)
		x.Save(w)
	default:
		panic(fmt.Errorf("unknown type: %#v", obj))
	}
}

// Load loads a new object.
//
// N.B. This function will panic on error.
func Load(r Reader) Object {
	switch hdr := LoadUint(r); hdr {
	case typeBool:
		return LoadBool(r)
	case typeInt:
		return LoadInt(r)
	case typeUint:
		return LoadUint(r)
	case typeFloat:
		return LoadFloat(r)
	case typeNil:
		return LoadNil(r)
	case typeRef:
		return ((*Ref)(nil)).load(r)
	case typeString:
		return ((*String)(nil)).load(r)
	case typeSlice:
		return ((*Slice)(nil)).load(r)
	case typeArray:
		return ((*Array)(nil)).load(r)
	case typeMap:
		return ((*Map)(nil)).load(r)
	case typeStruct:
		return ((*Struct)(nil)).load(r)
	case typeNoObjects: // Special for struct.
		return loadNoObjects(r)
	case typeMultipleObjects: // Special for struct.
		return ((*multipleObjects)(nil)).load(r)
	case typeInterface:
		return ((*Interface)(nil)).load(r)
	case typeType:
		return ((*Type)(nil)).load(r)
	case typeComplex:
		return ((*Complex)(nil)).load(r)
	default:
		// This is not a valid stream?
		panic(fmt.Errorf("unknown header: %d", hdr))
	}
}
