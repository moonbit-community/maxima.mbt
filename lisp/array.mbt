///|
/// `(make-array dims :initial-element x :element-type type :fill-pointer fp
/// :adjustable a)`
pub fn make_array(
  dims : Array[Int],
  initial? : Value = Nil,
  elt? : String = "t",
  fill? : Int,
) -> Value {
  let mut n = 1
  for d in dims {
    n *= d
  }
  let init = if initial is Nil {
    match elt {
      "fixnum" | "bit" | "integer" => Fix(0L)
      "double-float" | "flonum" => Flo(0.0)
      "character" => Char(' ')
      _ => Nil
    }
  } else {
    initial
  }
  Vec({ data: Array::make(n, init), dims, fill, elt })
}

///|
/// `(vector a b c ...)`
pub fn vector(xs : Array[Value]) -> Value {
  Vec({ data: xs.copy(), dims: [xs.length()], fill: None, elt: "t" })
}

///|
/// A fresh adjustable string with a fill pointer (for `vector-push-extend`).
pub fn make_string_buffer() -> Value {
  Vec({ data: [], dims: [0], fill: Some(0), elt: "character" })
}

///|
pub fn as_array(x : Value) -> LArray raise LispError {
  match x {
    Vec(a) => a
    _ => raise type_error(x, "array")
  }
}

///|
/// `(arrayp x)`
pub fn arrayp(x : Value) -> Bool {
  x is (Vec(_) | Str(_))
}

///|
/// `(vectorp x)`
pub fn vectorp(x : Value) -> Bool {
  match x {
    Vec(a) => a.dims.length() == 1
    Str(_) => true
    _ => false
  }
}

///|
fn row_major_index(a : LArray, idx : Array[Int]) -> Int raise LispError {
  if idx.length() != a.dims.length() {
    raise SimpleError("aref: wrong number of subscripts")
  }
  let mut k = 0
  for i, d in a.dims {
    if idx[i] < 0 || idx[i] >= d {
      raise SimpleError("aref: index \{idx[i]} out of bounds for dimension \{d}")
    }
    k = k * d + idx[i]
  }
  k
}

///|
/// `(aref a i ...)`
pub fn aref(x : Value, idx : Array[Int]) -> Value raise LispError {
  match x {
    Str(s) => Char(char_at(s, idx[0]))
    _ => {
      let a = as_array(x)
      a.data[row_major_index(a, idx)]
    }
  }
}

///|
/// `(aref a i)` for vectors.
pub fn aref1(x : Value, i : Int) -> Value raise LispError {
  match x {
    Vec(a) if a.dims.length() == 1 =>
      if i >= 0 && i < a.data.length() {
        a.data[i]
      } else {
        raise SimpleError("aref: index \{i} out of bounds")
      }
    _ => aref(x, [i])
  }
}

///|
/// `(setf (aref a i ...) v)`; returns v.
pub fn aset(x : Value, idx : Array[Int], v : Value) -> Value raise LispError {
  let a = as_array(x)
  a.data[row_major_index(a, idx)] = v
  v
}

///|
/// `(setf (aref a i) v)` for vectors.
pub fn aset1(x : Value, i : Int, v : Value) -> Value raise LispError {
  match x {
    Vec(a) if a.dims.length() == 1 && i >= 0 && i < a.data.length() => {
      a.data[i] = v
      v
    }
    _ => aset(x, [i], v)
  }
}

///|
/// `(array-dimensions a)` as a list.
pub fn array_dimensions(x : Value) -> Value raise LispError {
  match x {
    Str(s) => list([int(string_length(s))])
    _ => list(as_array(x).dims.map(d => int(d)))
  }
}

///|
/// `(array-dimension a k)`
pub fn array_dimension(x : Value, k : Int) -> Int raise LispError {
  match x {
    Str(s) => string_length(s)
    _ => as_array(x).dims[k]
  }
}

///|
/// `(array-rank a)`
pub fn array_rank(x : Value) -> Int raise LispError {
  match x {
    Str(_) => 1
    _ => as_array(x).dims.length()
  }
}

///|
/// `(array-total-size a)`
pub fn array_total_size(x : Value) -> Int raise LispError {
  match x {
    Str(s) => string_length(s)
    _ => as_array(x).data.length()
  }
}

///|
/// `(fill-pointer a)`
pub fn fill_pointer(x : Value) -> Int raise LispError {
  match as_array(x).fill {
    Some(f) => f
    None => raise SimpleError("array has no fill pointer")
  }
}

///|
/// `(setf (fill-pointer a) n)`
pub fn set_fill_pointer(x : Value, n : Int) -> Unit raise LispError {
  let a = as_array(x)
  while a.data.length() < n {
    a.data.push(Nil)
  }
  a.fill = Some(n)
}

///|
/// `(vector-push-extend v a)`; returns the index.
pub fn vector_push_extend(v : Value, x : Value) -> Int raise LispError {
  let a = as_array(x)
  let f = match a.fill {
    Some(f) => f
    None => a.data.length()
  }
  if f < a.data.length() {
    a.data[f] = v
  } else {
    a.data.push(v)
  }
  a.fill = Some(f + 1)
  a.dims = [f + 1]
  f
}

///|
/// `(vector-pop a)`
pub fn vector_pop(x : Value) -> Value raise LispError {
  let a = as_array(x)
  let f = fill_pointer(x)
  a.fill = Some(f - 1)
  a.data[f - 1]
}

///|
/// `(adjust-array a dims)` (data preserved in row-major order where
/// possible).
pub fn adjust_array(
  x : Value,
  dims : Array[Int],
  initial? : Value = Nil,
) -> Value raise LispError {
  let a = as_array(x)
  let mut n = 1
  for d in dims {
    n *= d
  }
  if a.dims.length() == 1 && dims.length() == 1 {
    while a.data.length() < n {
      a.data.push(initial)
    }
    while a.data.length() > n {
      a.data.pop() |> ignore
    }
  } else {
    let nd = Array::make(n, initial)
    // copy overlapping region
    let old_dims = a.dims
    let total = a.data.length()
    for k in 0..<total {
      // decode k in old dims
      let idx = Array::make(old_dims.length(), 0)
      let mut rem = k
      for j = old_dims.length() - 1; j >= 0; j = j - 1 {
        idx[j] = rem % old_dims[j]
        rem = rem / old_dims[j]
      }
      let mut ok = true
      let mut nk = 0
      for j, d in dims {
        if idx[j] >= d {
          ok = false
          break
        }
        nk = nk * d + idx[j]
      }
      if ok {
        nd[nk] = a.data[k]
      }
    }
    a.data = nd
  }
  a.dims = dims
  x
}

///|
/// Elements of a vector as a list (`(coerce v 'list)`).
pub fn vector_to_list(x : Value) -> Value raise LispError {
  match x {
    Str(s) => string_to_char_list(s)
    _ => {
      let a = as_array(x)
      let n = match a.fill {
        Some(f) => f
        None => a.data.length()
      }
      list_view(a.data[0:n])
    }
  }
}

///|
/// `(coerce list 'vector)`
pub fn list_to_vector(l : Value) -> Value {
  vector(list_to_array(l))
}

///|
/// `(elt seq i)` for lists, vectors and strings.
pub fn elt(s : Value, i : Int) -> Value raise LispError {
  match s {
    Nil | Cons(_) => nth(i, s)
    _ => aref1(s, i)
  }
}

///|
/// `(subseq seq start end)` for lists, vectors and strings.
pub fn subseq(s : Value, start : Int, end? : Int) -> Value raise LispError {
  match s {
    Str(str) => Str(substring(str, start, end?))
    Nil | Cons(_) => {
      let arr = list_to_array(s)
      let e = end.unwrap_or(arr.length())
      list_view(arr[start:e])
    }
    Vec(a) => {
      let n = match a.fill {
        Some(f) => f
        None => a.data.length()
      }
      let e = end.unwrap_or(n)
      if a.elt == "character" {
        Str(lstring(s) |> substring(start, end=e))
      } else {
        vector(a.data[start:e].to_array())
      }
    }
    _ => raise type_error(s, "sequence")
  }
}

///|
/// `(copy-seq s)`
pub fn copy_seq(s : Value) -> Value raise LispError {
  match s {
    Vec(a) => Vec({ data: a.data.copy(), dims: a.dims.copy(), fill: a.fill, elt: a.elt })
    Nil | Cons(_) => copy_list(s)
    _ => s
  }
}

// ---------------------------------------------------------------------------
// Structures

///|
/// Make a defstruct instance.
pub fn make_struct(stype : String, slots : Array[Value]) -> Value {
  Struct({ stype: intern(stype), slots })
}

///|
/// Read slot `i` of a struct.
pub fn struct_ref(x : Value, i : Int) -> Value raise LispError {
  match x {
    Struct(s) => s.slots[i]
    _ => raise type_error(x, "structure")
  }
}

///|
/// Write slot `i` of a struct; returns v.
pub fn struct_set(x : Value, i : Int, v : Value) -> Value raise LispError {
  match x {
    Struct(s) => {
      s.slots[i] = v
      v
    }
    _ => raise type_error(x, "structure")
  }
}

///|
/// Is x a struct of type `name`?
pub fn struct_typep(x : Value, name : String) -> Bool {
  match x {
    Struct(s) => s.stype.name == name
    _ => false
  }
}
