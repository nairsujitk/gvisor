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

package wire

import (
	"bytes"
	"fmt"
	"reflect"
	"testing"
)

func TestTypes(t *testing.T) {
	c := Complex(complex(1.0, 2.0))
	st := String("abc")
	fn := FieldName("abc")
	r0 := Ref{Root: 1}
	r1 := Ref{Root: 1, Dots: []Dot{Index(1)}}
	r2 := Ref{Root: 1, Dots: []Dot{Index(1), &fn}}
	sl := Slice{Length: 1, Capacity: 2, Ref: r0}
	a := Array{Contents: []Object{&st, &st, &st}}
	m := Map{Keys: []Object{&st}, Values: []Object{&st}}
	i := Interface{TypeID: 1, Value: &st}

	// Structs have special field manipulation.
	s0 := Struct{} // Empty struct.
	s0.Alloc(0)
	s1 := Struct{} // Three inline elements.
	s1.Alloc(1)
	*s1.Add() = Uint(1)
	s6 := Struct{} // Six elements (not inline).
	s6.Alloc(6)
	*s6.Add() = &c
	*s6.Add() = &r2
	*s6.Add() = &sl
	*s6.Add() = &a
	*s6.Add() = &m
	*s6.Add() = &i

	for _, obj := range []Object{
		Bool(false),
		Bool(true),
		^Int(^Uint(0) >> 1), // Smallest Int.
		Int(-1),
		Int(0),
		Uint(0),
		Int(1),
		Uint(1),
		Int(^Uint(0) >> 1), // Largest Int.
		^Uint(0),           // Largest Uint.
		Uint(1),
		Float(1.0),
		Nil{},
		&c,
		&st,
		&r0,
		&r1,
		&r2,
		&sl,
		&a,
		&m,
		&i,
		&s0,
		&s1,
		&s6,
	} {
		typ := reflect.TypeOf(obj)
		if typ.Kind() == reflect.Ptr {
			typ = typ.Elem()
		}
		t.Run(fmt.Sprintf("%s[%v]", typ.Name(), obj), func(t *testing.T) {
			b := new(bytes.Buffer)
			Save(b, obj) // Serialize the object.
			t.Logf("bytes: %v", b.Bytes())
			out := Load(b) // Load from the buffer.
			if !reflect.DeepEqual(obj, out) {
				t.Errorf("objects %#v and %#v do not match", obj, out)
			}
		})
	}
}
