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
	"fmt"
	"io"
	"io/ioutil"
	"reflect"
	"strings"

	"gvisor.dev/gvisor/pkg/state/wire"
)

func formatRef(x *wire.Ref, graph uint64, html bool) string {
	ref := fmt.Sprintf("g%dr%d", graph, x.Root)
	if len(x.Dots) > 0 {
		var buf strings.Builder
		buf.WriteString(ref)
		for _, component := range x.Dots {
			switch v := component.(type) {
			case *wire.FieldName:
				buf.WriteString(".")
				buf.WriteString(string(*v))
			case wire.Index:
				buf.WriteString(fmt.Sprintf("[%d]", v))
			default:
				panic(fmt.Sprintf("unreachable: switch should be exhaustive, unhandled case %v", reflect.TypeOf(component)))
			}
		}
		ref = buf.String()
	}
	if html {
		ref = fmt.Sprintf("<a href=\"#%s\">%s</a>", ref, ref)
	}
	return ref
}

func formatType(tid wire.Uint, graph uint64, html bool) string {
	ref := fmt.Sprintf("g%dt%d", graph, tid)
	if html {
		return fmt.Sprintf("<a href=\"#%s\">%s</a>", ref, ref)
	}
	return ref
}

// format formats a single object, for pretty-printing. It also returns whether
// the value is a non-zero value.
func format(graph uint64, depth int, encoded wire.Object, html bool) (string, bool) {
	switch x := encoded.(type) {
	case wire.Nil:
		return "nil", false
	case *wire.Ref:
		return formatRef(x, graph, html), true
	case *wire.Type:
		tabs := "\n" + strings.Repeat("\t", depth)
		items := make([]string, 0, len(x.Fields)+2)
		items = append(items, fmt.Sprintf("type %s {", x.Name))
		for i := 0; i < len(x.Fields); i++ {
			items = append(items, fmt.Sprintf("\t%d: %s,", i, string(x.Fields[i])))
		}
		items = append(items, "}")
		return strings.Join(items, tabs), true
	case *wire.Slice:
		return fmt.Sprintf("%s{len:%d,cap:%d}", formatRef(&x.Ref, graph, html), x.Length, x.Capacity), true
	case *wire.Array:
		if len(x.Contents) == 0 {
			return "[]", false
		}
		items := make([]string, 0, len(x.Contents)+2)
		zeros := make([]string, 0) // used to eliminate zero entries.
		items = append(items, "[")
		tabs := "\n" + strings.Repeat("\t", depth)
		for i := 0; i < len(x.Contents); i++ {
			item, ok := format(graph, depth+1, x.Contents[i], html)
			if ok {
				if len(zeros) > 0 {
					items = append(items, zeros...)
					zeros = nil
				}
				items = append(items, fmt.Sprintf("\t%s,", item))
			} else {
				zeros = append(zeros, fmt.Sprintf("\t%s,", item))
			}
		}
		if len(zeros) > 0 {
			items = append(items, fmt.Sprintf("\t... (%d zeros),", len(zeros)))
		}
		items = append(items, "]")
		return strings.Join(items, tabs), len(zeros) < len(x.Contents)
	case *wire.Struct:
		items := make([]string, 0, 2)
		items = append(items, fmt.Sprintf("struct[%s]{", formatType(x.TypeID, graph, html)))
		tabs := "\n" + strings.Repeat("\t", depth)
		allZero := true
		i := 0
		for field, ok := x.Next(); ok; field, ok = x.Next() {
			element, ok := format(graph, depth+1, field, html)
			allZero = allZero && !ok
			items = append(items, fmt.Sprintf("\t%d: %s,", i, element))
			i++
		}
		items = append(items, "}")
		return strings.Join(items, tabs), !allZero
	case *wire.Map:
		if len(x.Keys) == 0 {
			return "map{}", false
		}
		items := make([]string, 0, len(x.Keys)+2)
		items = append(items, "map{")
		tabs := "\n" + strings.Repeat("\t", depth)
		for i := 0; i < len(x.Keys); i++ {
			key, _ := format(graph, depth+1, x.Keys[i], html)
			value, _ := format(graph, depth+1, x.Values[i], html)
			items = append(items, fmt.Sprintf("\t%s: %s,", key, value))
		}
		items = append(items, "}")
		return strings.Join(items, tabs), true
	case *wire.Interface:
		element, _ := format(graph, depth+1, x.Value, html)
		return fmt.Sprintf("interface[%d]{%s}", x.TypeID, element), true
	default:
		// Must be a primitive; use reflection.
		return fmt.Sprintf("%v", encoded), true
	}
}

// PrettyPrint reads the state stream from r, and pretty prints to w.
func PrettyPrint(w io.Writer, r wire.Reader, html bool) error {
	// current graph ID.
	var graph uint64

	if html {
		fmt.Fprintf(w, "<pre>")
		defer fmt.Fprintf(w, "</pre>")
	}

	for {
		// Find the first object to begin generation.
		length, object, err := ReadHeader(r)
		if err == io.EOF {
			// Nothing else to do.
			break
		} else if err != nil {
			return err
		}
		if !object {
			graph++ // Increment the graph.
			if length > 0 {
				fmt.Fprintf(w, "(%d bytes non-object data)\n", length)
				io.Copy(ioutil.Discard, &io.LimitedReader{
					R: r,
					N: int64(length),
				})
			}
			continue
		}

		// Read & unmarshal the object.
		//
		// Note that this loop must match the general structure of the
		// loop in decode.go. But we don't register type information,
		// etc. and just print the raw structures.
		var (
			oid = objectID(1)
			tid = typeID(1)
		)
		for oid <= objectID(length) {
			// Unmarshal the object.
			encoded := wire.Load(r)

			// Is this a type?
			if _, ok := encoded.(*wire.Type); ok {
				str, _ := format(graph, 0, encoded, html)
				tag := fmt.Sprintf("g%dt%d", graph, tid)
				if html {
					tag = fmt.Sprintf("<a name=\"%s\">%s</a>", tag, tag)
				}
				if _, err := fmt.Fprintf(w, "%s = %s\n", tag, str); err != nil {
					return err
				}
				tid++
				continue
			}

			// Format the node.
			str, _ := format(graph, 0, encoded, html)
			tag := fmt.Sprintf("g%dr%d", graph, oid)
			if html {
				tag = fmt.Sprintf("<a name=\"%s\">%s</a>", tag, tag)
			}
			if _, err := fmt.Fprintf(w, "%s = %s\n", tag, str); err != nil {
				return err
			}
			oid++
		}
	}

	return nil
}

func printArray(s reflect.Value) (string, bool) {
	zero := reflect.Zero(s.Type().Elem()).Interface()
	z := "0"
	switch s.Type().Elem().Kind() {
	case reflect.Bool:
		z = "false"
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
	case reflect.Float32, reflect.Float64:
	default:
		return fmt.Sprintf("unexpected non-primitive type array: %#v", s.Interface()), true
	}

	zeros := 0
	items := make([]string, 0, s.Len())
	for i := 0; i <= s.Len(); i++ {
		if i < s.Len() && reflect.DeepEqual(s.Index(i).Interface(), zero) {
			zeros++
			continue
		}
		if zeros > 0 {
			if zeros <= 4 {
				for ; zeros > 0; zeros-- {
					items = append(items, z)
				}
			} else {
				items = append(items, fmt.Sprintf("(%d %ss)", zeros, z))
				zeros = 0
			}
		}
		if i < s.Len() {
			items = append(items, fmt.Sprintf("%v", s.Index(i).Interface()))
		}
	}
	return "[" + strings.Join(items, ",") + "]", zeros < s.Len()
}
