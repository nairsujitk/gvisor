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

package state

import (
	"fmt"
	"reflect"
	"sort"

	"gvisor.dev/gvisor/pkg/state/wire"
)

// TypeInfo is information about a specific type.
type TypeInfo struct {
	// Name is the name of the type. This is used for matching type
	// information during encoding and decoding, as well as dynamic
	// interface dispatch. This should be globally unique.
	Name string

	// Fields is the set of fields for the object. Calls to Sink.Save and
	// Source.Load must be made in-order with respect to these fields.
	Fields []string
}

// assertValid asserts that the TypeInfo is valid.
func (ti *TypeInfo) assertValid() {
	if ti.Name == "" {
		Failf("type has empty name")
	}
	fieldsCopy := make([]string, len(ti.Fields))
	for i := 0; i < len(ti.Fields); i++ {
		if ti.Fields[i] == "" {
			Failf("field has empty name")
		}
		fieldsCopy[i] = ti.Fields[i]
	}
	sort.Slice(fieldsCopy, func(i, j int) bool {
		return fieldsCopy[i] < fieldsCopy[j]
	})
	for i := range fieldsCopy {
		if i > 0 && fieldsCopy[i-1] == fieldsCopy[i] {
			panic(fmt.Errorf("duplicate field %s", fieldsCopy[i]))
		}
	}
}

// typeInfotoWire changes a TypeInfo to the wire format.
func typeInfoToWire(info TypeInfo) *wire.Type {
	newType := &wire.Type{
		Name:   wire.String(info.Name),
		Fields: make([]wire.String, 0, len(info.Fields)),
	}
	for _, f := range info.Fields {
		newType.Fields = append(newType.Fields, wire.String(f))
	}
	return newType
}

// wireToTypeIinfo changes a wire.Type to a TypeInfo.
func wireToTypeInfo(encoded *wire.Type) TypeInfo {
	info := TypeInfo{
		Name: string(encoded.Name),
	}
	for _, f := range encoded.Fields {
		info.Fields = append(info.Fields, string(f))
	}
	return info
}

// typeEntry is an entry in the typeDatabase.
type typeEntry struct {
	ID   typeID
	Info TypeInfo
}

// reconciledTypeEntry is a reconciled entry in the typeDatabase.
type reconciledTypeEntry struct {
	FieldOrder []int
	Info       TypeInfo
}

// typeEncodeDatabase is an internal TypeInfo database for encoding.
type typeEncodeDatabase struct {
	// byType maps by type to the typeEntry.
	byType map[reflect.Type]*typeEntry

	// lastID is the last used ID.
	lastID typeID
}

// makeTypeEncodeDatabase makes a typeDatabase.
func makeTypeEncodeDatabase() typeEncodeDatabase {
	return typeEncodeDatabase{
		byType: make(map[reflect.Type]*typeEntry),
	}
}

// typeDecodeDatabase is an internal TypeInfo database for decoding.
type typeDecodeDatabase struct {
	// byID maps by ID to type.
	byID []*reconciledTypeEntry

	// pending are entries that are pending validation by Lookup. These
	// will be reconciled with actual objects. Note that these will also be
	// used to lookup types by name, since they may not be reconciled and
	// there's little value to deleting from this map.
	pending []TypeInfo
}

// makeTypeDecodeDatabase makes a typeDatabase.
func makeTypeDecodeDatabase() typeDecodeDatabase {
	return typeDecodeDatabase{}
}

// Lookup looks up or registers the given object.
//
// The bool indicates whether this is an existing entry: false means the entry
// did not exist, and true means the entry did exist. If this bool is false and
// the returned typeEntry are nil, then the obj did not implement the Type
// interface.
func (tdb *typeEncodeDatabase) Lookup(obj reflect.Value) (SaverLoader, *typeEntry, bool) {
	t, ok := obj.Interface().(Type)
	if !ok {
		return nil, nil, false
	}
	sl, _ := t.(SaverLoader)
	typ := obj.Type()
	te, ok := tdb.byType[typ]
	if !ok {
		// Check for valid info.
		info := t.StateTypeInfo()
		info.assertValid()

		// Register the new type.
		tdb.lastID++
		te = &typeEntry{
			ID:   tdb.lastID,
			Info: info,
		}

		// All done.
		tdb.byType[typ] = te
		return sl, te, false
	}
	return sl, te, true
}

// Register adds a typeID entry.
func (tbd *typeDecodeDatabase) Register(info TypeInfo) {
	info.assertValid()
	tbd.pending = append(tbd.pending, info)
}

// LookupName looks up the type name.
func (tbd *typeDecodeDatabase) LookupName(id typeID) (string, bool) {
	if len(tbd.pending) < int(id) {
		return "", false
	}
	return tbd.pending[id-1].Name, true
}

// Lookup looks up or registers the given object.
//
// First, the typeID is searched to see if this has already been appropriately
// reconciled. If no, then a reconcilation will take place that may result in a
// field ordering. If a nil reconciledTypeEntry is returned from this method,
// then the object does not support the Type interface.
func (tbd *typeDecodeDatabase) Lookup(id typeID, obj reflect.Value) (SaverLoader, *reconciledTypeEntry) {
	t, ok := obj.Interface().(Type)
	if !ok {
		return nil, nil
	}
	sl, _ := t.(SaverLoader)
	if len(tbd.byID) >= int(id) && tbd.byID[id-1] != nil {
		// Already reconciled.
		return sl, tbd.byID[id-1]
	}
	// The ID has not been reconciled yet. That's fine. We need to make
	// sure it aligns with the current provided object.
	if len(tbd.pending) < int(id) {
		// This id was never registered. Probably an encoder error?
		Failf("typeDatabase does not contain id %d for object %#v", id, obj.Interface())
	}
	// Grow the byID list.
	if len(tbd.byID) < int(id) {
		tbd.byID = append(tbd.byID, make([]*reconciledTypeEntry, int(id)-len(tbd.byID))...)
	}
	pending := tbd.pending[id-1]
	info := t.StateTypeInfo()
	info.assertValid()
	if info.Name != pending.Name {
		// Are these the same type?
		Failf("typeDatabase contains conflicting definitions: %#v and %#v", info, pending)
	}
	rte := &reconciledTypeEntry{
		Info: TypeInfo{
			Name: info.Name,
		},
	}
	// If there are zero or one fields, then we skip allocating the field
	// slice. There is special handling for decoding in this case. If the
	// field name does not match, it will be caught in the general purpose
	// code below.
	if len(info.Fields) != len(pending.Fields) {
		Failf("type %s contains different fields: %#v and %#v", info.Name, info.Fields, pending.Fields)
	}
	if len(info.Fields) == 0 {
		tbd.byID[id-1] = rte // Save.
		return sl, rte
	}
	if len(info.Fields) == 1 && info.Fields[0] == pending.Fields[0] {
		tbd.byID[id-1] = rte // Save.
		return sl, rte
	}
	// For each field in the current object's information, match it to a
	// field in the destination object. We know from the assertion above
	// and the insertion on insertion to pending that neither field
	// contains any duplicates.
	fields := make([]int, len(info.Fields))
	for i, name := range info.Fields {
		fields[i] = -1 // Sentinel.
		// Is it an exact match?
		if pending.Fields[i] == name {
			fields[i] = i
			continue
		}
		// Find the matching field.
		for j, otherName := range pending.Fields {
			if name == otherName {
				fields[i] = j
				break
			}
		}
		if fields[i] == -1 {
			// The type name matches but we are lacking some common fields.
			Failf("type %s has mismatched fields: %v and %v", info.Name, info.Fields, pending.Fields)
		}
	}
	// The type has been reeconciled.
	rte.FieldOrder = fields
	tbd.byID[id-1] = rte
	return sl, rte
}

// globalTypeDatabase is used for dispatching interfaces on decode.
var globalTypeDatabase = make(map[string]reflect.Type)

// Register registers a type.
//
// This must be called on init and only done once.
func Register(t Type) {
	info := t.StateTypeInfo()
	info.assertValid()
	// Register must always be called on pointers.
	if reflect.TypeOf(t).Kind() != reflect.Ptr {
		Failf("Register must be called on pointers")
	}
	if reflect.TypeOf(t).Elem().Kind() == reflect.Struct {
		// Structs must implement SaverLoader.
		if _, ok := t.(SaverLoader); !ok {
			Failf("struct %T does not implement SaverLoader", t)
		}
	} else {
		// Non-structs must not have any fields.
		if len(info.Fields) != 0 {
			Failf("non-struct %T has non-zero fields %v", t, info.Fields)
		}
	}
	if _, ok := globalTypeDatabase[info.Name]; ok {
		Failf("conflicting typeDatabase entries for %#v: name conflict", t)
	}
	globalTypeDatabase[info.Name] = reflect.TypeOf(t)
}

// lookupType looks up a global type.
func lookupType(name string) (reflect.Type, bool) {
	typ, ok := globalTypeDatabase[name]
	return typ, ok
}
