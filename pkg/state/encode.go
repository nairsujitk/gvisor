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
	"context"
	"reflect"

	"gvisor.dev/gvisor/pkg/state/wire"
)

// objectEncodeState the type and identity of an object occupying a memory
// address range. This is the value type for addrSet, and the intrusive entry
// for the pending and deferred lists.
type objectEncodeState struct {
	// id is the assigned ID for this object.
	id objectID

	// obj is the object value. Note that this may be replaced if we
	// encounter an object that contains this object. When this happens (in
	// resolve), we will update existing references approprately, below,
	// and defer a re-encoding of the object.
	obj reflect.Value

	// encoded is the encoded value of this object. Note that this may not
	// be up to date if this object is still in the deferred list.
	encoded wire.Object

	// forceValue indicates whether this object should be encoded as a
	// value. This is used only for deferred encoding.
	forceValue bool

	// refs are the list of reference objects used by other objects
	// referring to this object. When the object is updated, these
	// references may be updated directly and automatically.
	refs []*wire.Ref

	pendingEntry
	deferredEntry
}

// encodeState is state used for encoding.
//
// The encoding process constructs a representation of the in-memory graph of
// objects before a single object is serialized. This is done to ensure that
// all references can be fully disambiguated. See resolve for more details.
type encodeState struct {
	// ctx is the encode context.
	ctx context.Context

	// w is the output stream.
	w wire.Writer

	// types is the type database.
	types typeEncodeDatabase

	// lastID is the last allocated object ID.
	lastID objectID

	// values tracks the address ranges occupied by objects, along with the
	// types of these objects. This is used to locate pointer targets,
	// including pointers to fields within another type.
	//
	// Multiple objects may overlap in memory iff the larger object fully
	// contains the smaller one, and the type of the smaller object matches
	// a field or array element's type at the appropriate offset. An
	// arbitrary number of objects may be nested in this manner.
	//
	// Note that this does not track zero-sized objects, those are tracked
	// by zeroValues below.
	values addrSet

	// zeroValues tracks zero-sized objects.
	zeroValues map[reflect.Type]*objectEncodeState

	// deferred is the list of objects to be encoded.
	deferred deferredList

	// pendingTypes is the list of types to be serialized. Serialization
	// will occur when all objects have been encoded, but before pending is
	// serialized.
	pendingTypes []*wire.Type

	// pending is the list of objects to be serialized. Serialization does
	// not actually occur until the full object graph is computed.
	pending pendingList

	// stats tracks time data.
	stats Stats
}

// isSameSizeParent returns true if child is a field value or element within
// parent. Only a struct or array can have a child value.
//
// isSameSizeParent deals with objects like this:
//
// struct child {
//     // fields..
// }
//
// struct parent {
//     c child
// }
//
// var p parent
// record(&p.c)
//
// Here, &p and &p.c occupy the exact same address range.
//
// Or like this:
//
// struct child {
//     // fields
// }
//
// var arr [1]parent
// record(&arr[0])
//
// Similarly, &arr[0] and &arr[0].c have the exact same address range.
//
// Precondition: parent and child must occupy the same memory.
func isSameSizeParent(parent reflect.Value, childType reflect.Type) bool {
	switch parent.Kind() {
	case reflect.Struct:
		for i := 0; i < parent.NumField(); i++ {
			field := parent.Field(i)
			if field.Type() == childType {
				return true
			}
			// Recurse through any intermediate types.
			if isSameSizeParent(field, childType) {
				return true
			}
			// Does it make sense to keep going if the first field
			// doesn't match? Yes, because there might be an
			// arbitrary number of zero-sized fields before we get
			// a match, and childType itself can be zero-sized.
		}
		return false
	case reflect.Array:
		// The only case where an array with more than one elements can
		// return true is if childType is zero-sized. In such cases,
		// it's ambiguous which element contains the match since a
		// zero-sized child object fully fits in any of the zero-sized
		// elements in an array... However since all elements are of
		// the same type, we only need to check one element.
		//
		// For non-zero-sized childTypes, parent.Len() must be 1, but a
		// combination of the precondition and an implicit comparison
		// between the array element size and childType ensures this.
		return parent.Len() > 0 && isSameSizeParent(parent.Index(0), childType)
	default:
		return false
	}
}

// nextID returns the next valid ID.
func (es *encodeState) nextID() objectID {
	es.lastID++
	return objectID(es.lastID)
}

// dummyAddr points to the dummy zero-sized address.
var dummyAddr = reflect.ValueOf(new(struct{})).Pointer()

// resolve records the address range occupied by an object.
func (es *encodeState) resolve(obj reflect.Value, ref *wire.Ref) {
	addr := obj.Pointer()

	// Is this a map pointer? Just record the single address. It is not
	// possible to take any pointers into the map internals.
	if obj.Kind() == reflect.Map {
		r := addrRange{addr, addr + 1}
		if !es.values.IsEmptyRange(r) {
			// Ensure the map types match.
			existing := es.values.LowerBoundSegment(addr).Value()
			if existing.obj.Type() != obj.Type() {
				Failf("overlapping map objects at %#v: [new object] %#v [existing object type] %s", r, obj, existing.obj)
			}

			// No sense recording refs, maps may not be replaced by
			// covering objects, they are maximal.
			ref.Root = wire.Uint(existing.id)
			return
		}

		// Record the map.
		oes := &objectEncodeState{
			id:         es.nextID(),
			obj:        obj,
			forceValue: true,
		}
		es.values.Add(r, oes)
		es.pending.PushBack(oes)
		es.deferred.PushBack(oes)

		// See above: no ref recording.
		ref.Root = wire.Uint(oes.id)
		return
	}

	// If not a map, then the object must be a pointer.
	if obj.Kind() != reflect.Ptr {
		Failf("attempt to record non-map and non-pointer object %#v", obj)
	}

	obj = obj.Elem() // Value from here.

	// Is this a zero-sized type?
	typ := obj.Type()
	size := typ.Size()
	if size == 0 {
		if addr == dummyAddr {
			// Zero-sized objects point to a dummy byte within the
			// runtime.  There's no sense recording this in the
			// address map.  We add this to the dedicated
			// zeroValues.
			//
			// Note that zero-sized objects must be *true*
			// zero-sized objects. They cannot be part of some
			// larger object. In that case, they are assigned a
			// 1-byte address at the end of the object.
			oes, ok := es.zeroValues[typ]
			if !ok {
				oes = &objectEncodeState{
					id:  es.nextID(),
					obj: obj,
				}
				es.zeroValues[typ] = oes
				es.pending.PushBack(oes)
				es.deferred.PushBack(oes)
			}

			// There's also no sense tracking back references. We
			// know that this is a true zero-sized object, and not
			// part of a larger container, so it will not change.
			ref.Root = wire.Uint(oes.id)
			return
		}
		size = 1 // See above.
	}

	// Calculate the container.
	end := addr + size
	r := addrRange{addr, end}
	if seg, _ := es.values.Find(addr); seg.Ok() {
		existing := seg.Value()
		switch {
		case seg.Start() == addr && seg.End() == end && obj.Type() == existing.obj.Type():
			// The object is a perfect match. Happy path. Avoid the
			// traversal and just return directly.
			ref.Root = wire.Uint(existing.id)
			existing.refs = append(existing.refs, ref)
			return

		case (seg.Start() < addr && seg.End() >= end) || (seg.Start() <= addr && seg.End() > end):
			// The previously registered object is larger than
			// this, no need to update. But we expect some
			// traversal below.

		case seg.Start() == addr && seg.End() == end:
			if !isSameSizeParent(obj, existing.obj.Type()) {
				break // Needs traversal.
			}
			fallthrough // Needs update.

		case (seg.Start() > addr && seg.End() <= end) || (seg.Start() >= addr && seg.End() < end):
			// Compute the traversal required & update references.
			dots := traverse(obj.Type(), existing.obj.Type(), addr, seg.Start())
			for _, ref := range existing.refs {
				ref.Dots = append(ref.Dots, dots...)
			}

			// The previously registered object is superseded by
			// this new object. We are guaranteed to not have any
			// mergeable neighbours in this segment set.
			if !raceEnabled {
				seg.SetRangeUnchecked(r)
			} else {
				// Add extra paranoid. This will be statically
				// removed at compile time unless a race build.
				es.values.Remove(seg)
				es.values.Add(r, existing)
				seg = es.values.LowerBoundSegment(addr)
			}

			// Update the object and redo the encoding.
			existing.obj = obj
			es.deferred.Remove(existing)
			es.deferred.PushBack(existing)

		default:
			// There is a non-sensical overlap.
			Failf("overlapping objects: [new object] %#v [existing object] %#v", obj, existing.obj)
		}

		// Compute the new reference, record and return it.
		ref.Root = wire.Uint(existing.id)
		ref.Dots = traverse(existing.obj.Type(), obj.Type(), seg.Start(), addr)
		existing.refs = append(existing.refs, ref)
		return
	}

	// The only remaining case is a pointer value that doesn't overlap with
	// any registered addresses. Create a new entry for it, and start
	// tracking the first reference we just created.
	oes := &objectEncodeState{
		id:  es.nextID(),
		obj: obj,
	}
	if !raceEnabled {
		es.values.AddWithoutMerging(r, oes)
	} else {
		// Merges should never happen. This is just enabled extra
		// sanity checks because the Merge function below will panic.
		es.values.Add(r, oes)
	}
	es.pending.PushBack(oes)
	es.deferred.PushBack(oes)
	ref.Root = wire.Uint(oes.id)
	oes.refs = append(oes.refs, ref)
	return
}

// traverse searches for a target object within a root object, where the target
// object is a struct field or array element within root, with potentially
// multiple intervening types. traverse returns the set of field or element
// traversals required to reach the target.
//
// Note that for efficiency, traverse returns the dots in the reverse order.
// That is, the first traversal required will be the last element of the list.
//
// Precondition: The target object must lie completely within the range defined
// by [rootAddr, rootAddr + sizeof(rootType)].
func traverse(rootType, targetType reflect.Type, rootAddr, targetAddr uintptr) []wire.Dot {
	// Recursion base case: the types actually match.
	if targetType == rootType && targetAddr == rootAddr {
		return nil
	}

	switch rootType.Kind() {
	case reflect.Struct:
		offset := targetAddr - rootAddr
		for i := rootType.NumField(); i > 0; i-- {
			field := rootType.Field(i - 1)
			// The first field from the end with an offset that is
			// smaller than or equal to our address offset is where
			// the target is located. Traverse from there.
			if field.Offset <= offset {
				dots := traverse(field.Type, targetType, rootAddr+field.Offset, targetAddr)
				fieldName := wire.FieldName(field.Name)
				return append(dots, &fieldName)
			}
		}
		// Should never happen; the target should be reachable.
		Failf("no field in root type %v contains target type %v", rootType, targetType)

	case reflect.Array:
		// Since arrays have homogenous types, all elements have the
		// same size and we can compute where the target lives. This
		// does not matter for the purpose of typing, but matters for
		// the purpose of computing the address of the given index.
		elemSize := int(rootType.Elem().Size())
		n := int(targetAddr-rootAddr) / elemSize // Relies on integer division rounding down.
		if rootType.Len() < n {
			Failf("traversal target of type %v @%x is beyond the end of the array type %v @%x with %v elements",
				targetType, targetAddr, rootType, rootAddr, rootType.Len())
		}
		dots := traverse(rootType.Elem(), targetType, rootAddr+uintptr(n*elemSize), targetAddr)
		return append(dots, wire.Index(n))

	default:
		// For any other type, there's no possibility of aliasing so if
		// the types didn't match earlier then we have an addresss
		// collision which shouldn't be possible at this point.
		Failf("traverse failed for root type %v and target type %v", rootType, targetType)
	}

	panic("unreachable")
}

// encodeMap encodes a map.
func (es *encodeState) encodeMap(obj reflect.Value) *wire.Map {
	l := obj.Len()
	encoded := &wire.Map{
		Keys:   make([]wire.Object, l),
		Values: make([]wire.Object, l),
	}
	for i, k := range obj.MapKeys() {
		v := obj.MapIndex(k)
		// Map keys must be encoded using the full value because the
		// type will be omitted after the first key.
		es.encodeObject(k, true, &encoded.Keys[i])
		es.encodeObject(v, true, &encoded.Values[i])
	}
	return encoded
}

// objectEncoder is for encoding structs.
type objectEncoder struct {
	// es is encodeState.
	es *encodeState

	// encoded is the encoded struct.
	encoded *wire.Struct
}

// save is called by the public methods on Sink.
func (oe *objectEncoder) save(obj reflect.Value) {
	fieldValue := oe.encoded.Add()
	oe.es.encodeObject(obj, false, fieldValue)
}

// encodeStruct encodes a composite object.
func (es *encodeState) encodeStruct(obj reflect.Value) *wire.Struct {
	// Ensure that the obj is addressable. There are two cases when it is
	// not. First, is when this is dispatched via SaveValue. Second, when
	// this is a map key as a struct. Either way, we need to make a copy to
	// obtain an addressable value.
	if !obj.CanAddr() {
		localObj := reflect.New(obj.Type())
		localObj.Elem().Set(obj)
		obj = localObj.Elem()
	}

	// Look the type up in the database.
	sl, te, ok := es.types.Lookup(obj.Addr())
	if sl == nil || te == nil {
		if obj.NumField() == 0 {
			// Allow unregistered anonymous, empty structs. This
			// will just return success without ever invoking the
			// passed function. This uses the immutable EmptyStruct
			// variable to prevent an allocation in this case.
			s := &wire.Struct{}
			s.Alloc(0)
			return s
		}
		// We need a SaverLoader for struct types.
		Failf("struct %T does not implement SaverLoader", obj.Interface())
	}
	if !ok {
		// Queue the type to be serialized.
		es.pendingTypes = append(es.pendingTypes, typeInfoToWire(te.Info))
	}

	// Invoke the provided saver.
	s := &wire.Struct{
		TypeID: wire.Uint(te.ID),
	}
	s.Alloc(len(te.Info.Fields))
	oe := objectEncoder{
		es:      es,
		encoded: s,
	}
	es.stats.start(te.ID)
	defer es.stats.done()
	sl.StateSave(Sink{internal: oe})

	return oe.encoded
}

// encodeArray encodes an array.
func (es *encodeState) encodeArray(obj reflect.Value) *wire.Array {
	l := obj.Len()
	encoded := &wire.Array{
		Contents: make([]wire.Object, l),
	}
	for i := 0; i < l; i++ {
		// We need to encode the full value because arrays are encoded
		// using the type information from only the first element.
		es.encodeObject(obj.Index(i), true, &encoded.Contents[i])
	}
	return encoded
}

// encodeInterface encodes an interface.
//
// Precondition: the value is not nil.
func (es *encodeState) encodeInterface(obj reflect.Value) wire.Object {
	// Dereference the object.
	obj = reflect.ValueOf(obj.Interface())
	if !obj.IsValid() {
		// This is the nil object.
		return wire.Nil{}
	}

	// We have an interface value here. How do we save that? We resolve the
	// underlying type and save it as a dispatchable.
	_, te, ok := es.types.Lookup(obj)
	if te == nil {
		Failf("unregistered type %s", obj.Type())
	}
	if !ok {
		// See encodeStruct.
		es.pendingTypes = append(es.pendingTypes, typeInfoToWire(te.Info))
	}

	// Encode the object again.
	i := &wire.Interface{
		TypeID: wire.Uint(te.ID),
	}
	if obj.IsNil() {
		i.Value = wire.Nil{}
	} else {
		es.encodeObject(obj, false, &i.Value)
	}
	return i
}

// isPrimitive returns true if this is a primitive object, or a composite
// object composed entirely of primitives.
func isPrimitive(typ reflect.Type) bool {
	switch typ.Kind() {
	case reflect.Ptr:
		// Pointers are always treated as primitive types because we
		// won't encode directly from here. Returning true here won't
		// prevent the object from being encoded correctly.
		return true
	case reflect.Bool:
		return true
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		return true
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
		return true
	case reflect.Float32, reflect.Float64:
		return true
	case reflect.Complex64, reflect.Complex128:
		return true
	case reflect.String:
		return true
	case reflect.Slice:
		// The slice itself a primitive, but not necessarily the array
		// that points to. This is similar to a pointer.
		return true
	case reflect.Array:
		// We cannot treat an array as a primitive, because it may be
		// composed of structures or other things with side-effects.
		return isPrimitive(typ.Elem())
	case reflect.Interface:
		// The interface may be nil or point to a primitive, but we
		// need to encode it anyways to have type information.
		return false
	case reflect.Struct:
		return false
	case reflect.Map:
		return isPrimitive(typ.Key()) && isPrimitive(typ.Elem())
	default:
		Failf("unknown type %v", typ)
	}
	panic("unreachable")
}

// encodeObject encodes an object.
//
// If forceValue is true, then the object will always be encoded fully.
func (es *encodeState) encodeObject(obj reflect.Value, forceValue bool, dest *wire.Object) {
	// Fast path: zeros.
	if obj.IsZero() && !forceValue && isPrimitive(obj.Type()) {
		*dest = wire.Nil{}
		return
	}

	switch obj.Kind() {
	case reflect.Ptr: // Fast path: first.
		if obj.IsNil() {
			// May be in an array or elsewhere such that a value is
			// required. So we encode as a reference to the zero
			// object, which does not exist. Note that this has to
			// be handled correctly in the decode path as well.
			*dest = new(wire.Ref)
			return
		}
		r := new(wire.Ref)
		es.resolve(obj, r)
		*dest = r
	case reflect.Bool:
		*dest = wire.Bool(obj.Bool())
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		*dest = wire.Int(obj.Int())
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
		*dest = wire.Uint(obj.Uint())
	case reflect.Float32, reflect.Float64:
		*dest = wire.Float(obj.Float())
	case reflect.Complex64, reflect.Complex128:
		c := wire.Complex(obj.Complex())
		*dest = &c // Needs alloc.
	case reflect.String:
		s := wire.String(obj.String())
		*dest = &s // Needs alloc.
	case reflect.Array:
		*dest = es.encodeArray(obj)
	case reflect.Slice:
		// Don't bother if no capacity. Note that we do need to provide
		// a wire.Slice type here as "forceValue" may be true. If
		// "forceValue" is false, then this would have been caught by
		// the IsZero check above and we would have return wire.Nil{}.
		if obj.IsNil() {
			*dest = &wire.Slice{}
			return
		}
		// Slices need pointer resolution.
		s := &wire.Slice{
			Capacity: wire.Uint(obj.Cap()),
			Length:   wire.Uint(obj.Len()),
		}
		es.resolve(arrayFromSlice(obj), &s.Ref)
		*dest = s
	case reflect.Interface:
		*dest = es.encodeInterface(obj)
	case reflect.Struct:
		*dest = es.encodeStruct(obj)
	case reflect.Map:
		if forceValue {
			*dest = es.encodeMap(obj)
			return
		}
		if obj.IsNil() {
			*dest = wire.Nil{}
			return
		}
		r := new(wire.Ref)
		es.resolve(obj, r)
		*dest = r
	default:
		Failf("unknown object %#v", obj.Interface())
	}
}

// Save serializes the object graph rooted at obj.
func (es *encodeState) Save(obj reflect.Value) {
	es.stats.init()
	defer es.stats.fini(func(id typeID) string {
		return string(es.pendingTypes[id-1].Name)
	})

	// Resolve the first object, which should queue a pile of additional
	// objects on the pending list. All queued objects should be fully
	// resolved, and we should be able to serialize after this call.
	var root wire.Ref
	es.resolve(obj.Addr(), &root)

	// Encode the graph.
	var oes *objectEncodeState
	if err := safely(func() {
		for {
			oes = es.deferred.Front()
			if oes == nil {
				break
			}

			// Remove and encode the object. Note that as a result
			// of this encoding, the object may be enqueued on the
			// deferred list yet again. That's expected, and why it
			// is removed first.
			es.deferred.Remove(oes)
			es.encodeObject(oes.obj, oes.forceValue, &oes.encoded)
		}
	}); err != nil {
		// Include the object in the error message.
		maybeFailf(err, "encoding error at object %#v: %v", oes.obj.Interface(), err)
	}

	// Check that items are pending.
	if es.pending.Front() == nil {
		Failf("pending is empty?")
	}

	// Write the header with the number of objects.
	if err := WriteHeader(es.w, uint64(es.lastID), true); err != nil {
		Failf("error writing header: %v", err)
	}

	// Serialize all pending types and pending objects. Note that we don't
	// bother removing from this list as we walk it because that just
	// wastes time. It will not change after this point.
	var id objectID
	if err := safely(func() {
		for _, wt := range es.pendingTypes {
			// Encode the type.
			wire.Save(es.w, wt)
		}
		for oes = es.pending.Front(); oes != nil; oes = oes.pendingEntry.Next() {
			id++ // First object is 1.
			if oes.id != id {
				Failf("expected id %d, got %d", id, oes.id)
			}

			// Marshall the object.
			wire.Save(es.w, oes.encoded)
		}
	}); err != nil {
		// Include the object and the error.
		maybeFailf(err, "error serializing object %#v: %v", oes.encoded, err)
	}

	// Check what we wrote.
	if id != es.lastID {
		Failf("expected %d objects, wrote %d", es.lastID, id)
	}
}

// WriteHeader writes a header.
//
// Each object written to the statefile should be prefixed with a header. In
// order to generate statefiles that play nicely with debugging tools, raw
// writes should be prefixed with a header with object set to false and the
// appropriate length. This will allow tools to skip these regions.
func WriteHeader(w wire.Writer, length uint64, object bool) error {
	// The lowest-order bit encodes whether this is a valid object. This is
	// a purely internal convention, but allows the object flag to be
	// returned from ReadHeader.
	length = length << 1
	if object {
		length |= 0x1
	}

	// Write a header.
	hdr := wire.Uint(length)
	return safely(func() {
		hdr.Save(w)
	})
}

// pendingMapper is for the pending list.
type pendingMapper struct{}

func (pendingMapper) linkerFor(oes *objectEncodeState) *pendingEntry { return &oes.pendingEntry }

// deferredMapper is for the deferred list.
type deferredMapper struct{}

func (deferredMapper) linkerFor(oes *objectEncodeState) *deferredEntry { return &oes.deferredEntry }

// addrSetFunctions is used by addrSet.
type addrSetFunctions struct{}

func (addrSetFunctions) MinKey() uintptr {
	return 0
}

func (addrSetFunctions) MaxKey() uintptr {
	return ^uintptr(0)
}

func (addrSetFunctions) ClearValue(val **objectEncodeState) {
	*val = nil
}

func (addrSetFunctions) Merge(r1 addrRange, val1 *objectEncodeState, r2 addrRange, val2 *objectEncodeState) (*objectEncodeState, bool) {
	if val1.obj == val2.obj {
		// This, should never happen. It would indicate that the same
		// object exists in two non-contiguous address ranges. Note
		// that this assertion can only be triggered if the race
		// detector is enabled.
		Failf("unexpected merge in addrSet @ %v and %v: %#v and %#v", r1, r2, val1.obj, val2.obj)
	}
	// Reject the merge.
	return val1, false
}

func (addrSetFunctions) Split(r addrRange, val *objectEncodeState, _ uintptr) (*objectEncodeState, *objectEncodeState) {
	// A split should never happen: we don't remove ranges.
	Failf("unexpected split in addrSet @ %v: %#v", r, val.obj)
	panic("unreachable")
}
