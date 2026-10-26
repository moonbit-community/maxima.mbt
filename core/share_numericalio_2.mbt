// Port of share/numericalio/numericalio.lisp (Robert Dodier, 2005): read
// and write matrices, arrays and lists in text and binary files.
//
// File streams. The port's file streams are those of stringproc
// (share_stringproc.mbt): the file is read at open time and written at
// close/flush time. A binary stream is a character stream whose characters
// are octets (latin-1); it is recorded in share_numericalio__binary so that
// READ-BYTE and WRITE-BYTE can tell. CL's WITH-OPEN-FILE becomes a stream
// over the file contents, written back at the end for output.

///|
let share_numericalio__binary : Array[LStream] = []

///|
fn share_numericalio__binaryp(s : Value) -> Bool {
  match s {
    Stream(st) => share_numericalio__binary.iter().any(b => physical_equal(b, st))
    _ => false
  }
}

///|
/// (read-byte s nil 'eof)
fn share_numericalio__read_byte(s : Value) -> Value raise {
  match read_char(stream=s, eof_value=q_eof) {
    Char(c) => Fix(c.to_int().to_int64())
    _ => q_eof
  }
}

///|
/// (write-byte b s)
fn share_numericalio__write_byte(b : Value, s : Value) -> Unit raise {
  write_char(Int::unsafe_to_char(to_int(b)), stream=s)
}

///|
fn share_numericalio__latin1() -> Value {
  sym("latin-1")
}

///|
/// An input stream over the file PATH (text, or octets for binary), or NIL
/// if the file does not exist (:if-does-not-exist nil).
fn share_numericalio__open_input(path : String, binary : Bool) -> Value raise {
  if !probe_file(path) {
    return Nil
  }
  let bytes = share_stringproc__read_file_bytes(path)
  let text : Array[Char] = if binary {
    let cs : Array[Char] = []
    for b in bytes {
      cs.push(Int::unsafe_to_char(b.to_int()))
    }
    cs
  } else {
    share_stringproc__decode_bytes(
      share_stringproc__bytes_to_ints(bytes),
      sym("utf-8"),
    )
  }
  let st : LStream = {
    input: chars_to_string(text),
    pos: 0,
    unread: [],
    out: None,
    name: path,
    sink: None,
    column: 0,
    line: 1,
    is_input: true,
    eof: false,
  }
  share_stringproc__files.push((
    st,
    {
      path,
      enc: if binary {
        share_numericalio__latin1()
      } else {
        sym("utf-8")
      },
      prefix: b"",
      buf: StringBuilder::new(),
      output: false,
      text,
      closed: false,
    },
  ))
  if binary {
    share_numericalio__binary.push(st)
  }
  Stream(st)
}

///|
/// An output stream on the file PATH.
fn share_numericalio__open_output(
  path : String,
  binary : Bool,
  append : Bool,
) -> Value raise {
  let s = share_stringproc__open_output(
    path,
    if binary {
      share_numericalio__latin1()
    } else {
      sym("utf-8")
    },
    append,
  )
  if binary {
    match s {
      Stream(st) => share_numericalio__binary.push(st)
      _ => ()
    }
  }
  s
}

///|
/// (close s) on a file stream: write output to the file.
fn share_numericalio__close(s : Value) -> Unit raise {
  match share_stringproc__file_of(s) {
    Some(f) => {
      share_stringproc__write_out(f)
      f.closed = true
    }
    None => ()
  }
}

///|
/// WITH-OPEN-FILE for input: call BODY with the stream (NIL when the file
/// does not exist).
fn share_numericalio__with_input_file(
  file_name : Value,
  mode : Value,
  body : (Value) -> Value raise,
) -> Value raise {
  let in_ = share_numericalio__open_input(lstring(file_name), !eq(mode, q_text))
  defer {
    if in_.truthy() {
      share_numericalio__close(in_) catch {
        _ => ()
      }
    }
  }
  body(in_)
}

///|
fn d_assume_external_byte_order(x : Value) -> Value raise {
  if eq(x, q_d_lsb) {
    define_external_byte_order(q_kw_lsb)
  } else if eq(x, q_d_msb) {
    define_external_byte_order(q_kw_msb)
  } else {
    merror(
      Str("assume_external_byte_order: unrecognized byte order flag: ~a"),
      list1(x),
    )
  }
}

///|
fn lisp_or_declared_maxima_array_p(x : Value) -> Value raise {
  if arrayp(x) {
    t
  } else {
    mget(x, q_array)
  }
}

// THESE FILE-OPENING FUNCTIONS WANT TO BE MOVED TO STRINGPROC (HOME OF OTHER
// SUCH FUNCTIONS) !!

///|
fn d_openw_binary(file : Value) -> Value raise {
  share_numericalio__open_output(lstring(file), true, false)
}

///|
fn d_opena_binary(file : Value) -> Value raise {
  share_numericalio__open_output(lstring(file), true, true)
}

///|
fn d_openr_binary(file : Value) -> Value raise {
  let path = lstring(file)
  let s = share_numericalio__open_input(path, true)
  if s is Nil {
    raise share_stringproc__file_error(path, "No such file or directory")
  }
  s
}

// -------------------- read functions --------------------

// ---- functions to read a matrix

///|
fn d_read_matrix(stream_or_filename : Value, args : Value) -> Value raise {
  if d_matrixp(car(args)).truthy() {
    let m = car(args)
    let sep_ch_flag = cadr(args)
    let nrow = length(cdr(m))
    let ncol = if nrow > 0 { length(cdadr(m)) } else { 0 }
    let l = d_read_list(
      stream_or_filename,
      list([sep_ch_flag, int(nrow * ncol)]),
    )
    // COPYING DATA HERE !!
    fill_matrix_from_list(l, m, int(nrow), int(ncol))
  } else {
    let sep_ch_flag = car(args)
    let rows_list = cdr(d_read_nested_list(stream_or_filename, sep_ch_flag~))
    let rows_list_nonempty = remove_if(
      x => num_eq(d_length(x), Fix(0L)),
      rows_list,
    )
    cons(list1(q_d_matrix), rows_list_nonempty)
  }
}

///|
fn d_read_binary_matrix(stream_or_filename : Value, m : Value) -> Value raise {
  if d_matrixp(m).truthy() {
    let nrow = length(cdr(m))
    let ncol = if nrow > 0 { length(cdadr(m)) } else { 0 }
    let l = d_read_binary_list(stream_or_filename, list1(int(nrow * ncol)))
    // COPYING DATA HERE !!
    fill_matrix_from_list(l, m, int(nrow), int(ncol))
  } else {
    merror(
      Str("read_binary_matrix: expected a matrix, found ~a instead"),
      list1(share_numericalio__type_of(m)),
    )
  }
}

///|
/// A rough (type-of x) for messages.
fn share_numericalio__type_of(x : Value) -> Value {
  match x {
    Nil => q_null
    Sym(_) => q_symbol
    Cons(_) => q_cons
    Fix(_) => q_fixnum
    Big(_) => q_bignum
    Flo(_) => q_double_float
    Str(_) => sym("string")
    _ => q_t
  }
}

///|
fn fill_matrix_from_list(
  l : Value,
  m : Value,
  nrow : Value,
  ncol : Value,
) -> Value raise {
  let mut k = 0
  for i in 0..<to_int(nrow) {
    let row = nth(i + 1, m)
    for j in 0..<to_int(ncol) {
      rplaca(nthcdr(j + 1, row), nth(k + 1, l)) |> ignore
      k = k + 1
    }
  }
  m
}

// ---- functions to read a Lisp array or Maxima declared array

///|
fn d_read_array(stream_or_filename : Value, args : Value) -> Value raise {
  if args.truthy() && lisp_or_declared_maxima_array_p(car(args)).truthy() {
    let a = car(args)
    let sep_ch_flag = if cdr(args).truthy() { cadr(args) } else { Nil }
    read_into_existing_array(stream_or_filename, a, sep_ch_flag, q_text)
  } else {
    let sep_ch_flag = if args.truthy() { car(args) } else { Nil }
    read_and_return_new_array(stream_or_filename, sep_ch_flag, q_text)
  }
}

///|
fn d_read_binary_array(file_name : Value, args : Value) -> Value raise {
  if car(args).truthy() {
    read_into_existing_array(file_name, car(args), Nil, q_binary)
  } else {
    read_and_return_new_array(file_name, Nil, q_binary)
  }
}

///|
fn read_into_existing_array(
  file_name : Value,
  a : Value,
  sep_ch_flag : Value,
  mode : Value,
) -> Value raise {
  let a = if !arrayp(a) { get(mget(a, q_array), q_array) } else { a }
  let mut n : Value = Fix(1L)
  for d in array_dimensions(a).iter() {
    n = num_mul(n, d)
  }
  read_into_existing_array_size_known(file_name, a, sep_ch_flag, mode, n)
  |> ignore
  q_d_done
}

///|
fn read_into_existing_array_size_known(
  stream_or_filename : Value,
  a : Value,
  sep_ch_flag : Value,
  mode : Value,
  n : Value,
) -> Value raise {
  if streamp(stream_or_filename) {
    read_into_existing_array_size_known_from_stream(
      stream_or_filename,
      a,
      sep_ch_flag,
      mode,
      n,
    )
  } else {
    let file_name = require_string(stream_or_filename)
    share_numericalio__with_input_file(file_name, mode, in_ => if in_.truthy() {
      read_into_existing_array_size_known_from_stream(
        in_,
        a,
        sep_ch_flag,
        mode,
        n,
      )
    } else {
      merror(Str("read_array: no such file `~a'"), list1(file_name))
    })
  }
}

///|
/// (setf (row-major-aref a i) x)
fn share_numericalio__set_row_major(a : Value, i : Int, x : Value) -> Unit raise {
  match a {
    Vec(arr) => arr.data[i] = x
    _ => raise LispError::SimpleError("not an array: " + prin1_to_string(a))
  }
}

///|
fn read_into_existing_array_size_known_from_stream(
  in_ : Value,
  a : Value,
  sep_ch_flag : Value,
  mode : Value,
  n : Value,
) -> Value raise {
  let sep_ch = get_input_sep_ch(sep_ch_flag, in_)
  if eq(mode, q_text) {
    reset_for_parse_next_element() |> ignore
  }
  for i in 0..<to_int(n) {
    let x = if eq(mode, q_text) {
      parse_next_element(in_, sep_ch)
    } else {
      read_float_64(in_)
    }
    if eq(x, q_eof) {
      return a
    }
    share_numericalio__set_row_major(a, i, x)
  }
  Nil
}

///|
fn read_into_existing_array_size_unknown_from_stream(
  in_ : Value,
  a : Value,
  sep_ch : Value,
  mode : Value,
) -> Value raise {
  if eq(mode, q_text) {
    reset_for_parse_next_element() |> ignore
  }
  while true {
    let x = if eq(mode, q_text) {
      parse_next_element(in_, sep_ch)
    } else {
      read_float_64(in_)
    }
    if eq(x, q_eof) {
      return a
    }
    vector_push_extend(x, a) |> ignore
  }
  a
}

///|
fn read_and_return_new_array(
  stream_or_filename : Value,
  sep_ch_flag : Value,
  mode : Value,
) -> Value raise {
  if streamp(stream_or_filename) {
    read_and_return_new_array_from_stream(stream_or_filename, sep_ch_flag, mode)
  } else {
    let file_name = require_string(stream_or_filename)
    share_numericalio__with_input_file(file_name, mode, in_ => if in_.truthy() {
      read_and_return_new_array_from_stream(in_, sep_ch_flag, mode)
    } else {
      merror(Str("read_array: no such file `~a'"), list1(file_name))
    })
  }
}

///|
fn read_and_return_new_array_from_stream(
  in_ : Value,
  sep_ch_flag : Value,
  mode : Value,
) -> Value raise {
  let a = make_array([0], fill=0)
  let sep_ch = if eq(mode, q_text) {
    get_input_sep_ch(sep_ch_flag, in_)
  } else {
    Nil
  }
  read_into_existing_array_size_unknown_from_stream(in_, a, sep_ch, mode)
}

// ---- functions to read a Maxima undeclared array

///|
fn d_read_hashed_array(
  stream_or_filename : Value,
  a : Value,
  sep_ch_flag? : Value = Nil,
) -> Value raise {
  if streamp(stream_or_filename) {
    read_hashed_array_from_stream(stream_or_filename, a, sep_ch_flag)
  } else {
    let file_name = require_string(stream_or_filename)
    share_numericalio__with_input_file(file_name, q_text, in_ => if in_.truthy() {
      read_hashed_array_from_stream(in_, a, sep_ch_flag)
    } else {
      merror(Str("read_hashed_array no such file `~a'"), list1(file_name))
    })
  }
}

///|
fn read_hashed_array_from_stream(
  in_ : Value,
  a : Value,
  sep_ch_flag : Value,
) -> Value raise {
  let sep_ch = get_input_sep_ch(sep_ch_flag, in_)
  while true {
    let line = match read_line(stream=in_) {
      Some(s) => s
      None => break
    }
    let l = make_mlist_from_string(Str(line), sep_ch)
    if num_gt(d_length(l), Fix(0L)) {
      let key = d_first(l)
      if num_eq(d_length(l), Fix(1L)) {
        arrstore(list2(list2(a, q_array), key), Nil) |> ignore
      } else {
        arrstore(list2(list2(a, q_array), key), d_rest(l)) |> ignore
      }
    }
  }
  a
}

// ---- functions to read a list or nested list

///|
fn d_read_nested_list(
  stream_or_filename : Value,
  sep_ch_flag? : Value = Nil,
) -> Value raise {
  if streamp(stream_or_filename) {
    read_nested_list_from_stream(stream_or_filename, sep_ch_flag)
  } else {
    let file_name = require_string(stream_or_filename)
    share_numericalio__with_input_file(file_name, q_text, in_ => if in_.truthy() {
      read_nested_list_from_stream(in_, sep_ch_flag)
    } else {
      merror(Str("read_nested_list: no such file `~a'"), list1(file_name))
    })
  }
}

///|
fn read_nested_list_from_stream(in_ : Value, sep_ch_flag : Value) -> Value raise {
  let sep_ch = get_input_sep_ch(sep_ch_flag, in_)
  let mut a : Value = Nil
  while true {
    match read_line(stream=in_) {
      None => break
      Some(l) => a = cons(make_mlist_from_string(Str(l), sep_ch), a)
    }
  }
  cons(list2(q_mlist, q_simp), nreverse(a))
}

///|
fn d_read_list(stream_or_filename : Value, args : Value) -> Value raise {
  if d_listp(car(args)).truthy() {
    let l = car(args)
    let sep_ch_flag = cadr(args)
    let n = if caddr(args).truthy() { caddr(args) } else { d_length(l) }
    read_into_existing_list(stream_or_filename, l, sep_ch_flag, q_text, n)
  } else if integerp(car(args)) {
    let n = car(args)
    read_list(stream_or_filename, Nil, q_text, n)
  } else {
    let sep_ch_flag = car(args)
    let n = cadr(args)
    read_list(stream_or_filename, sep_ch_flag, q_text, n)
  }
}

///|
fn read_into_existing_list(
  stream_or_filename : Value,
  l : Value,
  sep_ch_flag : Value,
  mode : Value,
  n : Value,
) -> Value raise {
  if streamp(stream_or_filename) {
    read_into_existing_list_from_stream(
      stream_or_filename,
      l,
      sep_ch_flag,
      mode,
      n,
    )
  } else {
    let file_name = require_string(stream_or_filename)
    share_numericalio__with_input_file(file_name, mode, in_ => if in_.truthy() {
      read_into_existing_list_from_stream(in_, l, sep_ch_flag, mode, n)
    } else {
      merror(Str("read_list: no such file `~a'"), list1(file_name))
    })
  }
}

///|
fn read_into_existing_list_from_stream(
  in_ : Value,
  l : Value,
  sep_ch_flag : Value,
  mode : Value,
  n : Value,
) -> Value raise {
  let sep_ch = if eq(mode, q_text) {
    get_input_sep_ch(sep_ch_flag, in_)
  } else {
    Nil
  }
  if eq(mode, q_text) {
    reset_for_parse_next_element() |> ignore
  }
  for i in 0..<to_int(n) {
    let x = if eq(mode, q_text) {
      parse_next_element(in_, sep_ch)
    } else {
      read_float_64(in_)
    }
    if eq(x, q_eof) {
      break
    }
    rplaca(nthcdr(i + 1, l), x) |> ignore
  }
  l
}

///|
fn read_list(
  stream_or_filename : Value,
  sep_ch_flag : Value,
  mode : Value,
  n : Value,
) -> Value raise {
  if streamp(stream_or_filename) {
    read_list_from_stream(stream_or_filename, sep_ch_flag, mode, n)
  } else {
    let file_name = require_string(stream_or_filename)
    share_numericalio__with_input_file(file_name, mode, in_ => if in_.truthy() {
      read_list_from_stream(in_, sep_ch_flag, mode, n)
    } else {
      merror(Str("read_list: no such file `~a'"), list1(file_name))
    })
  }
}

///|
fn read_list_from_stream(
  in_ : Value,
  sep_ch_flag : Value,
  mode : Value,
  n : Value,
) -> Value raise {
  let mut n = n
  let sep_ch = if eq(mode, q_text) {
    get_input_sep_ch(sep_ch_flag, in_)
  } else {
    Nil
  }
  if eq(mode, q_text) {
    reset_for_parse_next_element() |> ignore
  }
  let mut a : Value = Nil
  while true {
    if n.truthy() && eql(n, Fix(0L)) {
      break
    }
    let x = if eq(mode, q_text) {
      parse_next_element(in_, sep_ch)
    } else {
      read_float_64(in_)
    }
    if eq(x, q_eof) {
      break
    }
    a = cons(x, a)
    if n.truthy() {
      n = num_sub(n, Fix(1L))
    }
  }
  cons(list2(q_mlist, q_simp), nreverse(a))
}

///|
fn d_read_binary_list(stream_or_filename : Value, args : Value) -> Value raise {
  if d_listp(car(args)).truthy() {
    let l = car(args)
    let n = if cadr(args).truthy() { cadr(args) } else { d_length(l) }
    read_into_existing_list(stream_or_filename, l, Nil, q_binary, n)
  } else {
    let n = car(args)
    read_list(stream_or_filename, Nil, q_binary, n)
  }
}

// ---- functions to read a structure

// The first line of the source names the fields and the lines after it hold
// one value per field. READ_STRUCT gathers each column into a list and
// returns one structure whose fields are those lists.

///|
fn d_read_struct(stream_or_filename : Value, args : Value) -> Value raise {
  let mut name : Value = Nil
  let mut sep_ch_flag : Value = Nil
  for arg in args.iter() {
    if read_struct_separator_flag_p(arg).truthy() {
      sep_ch_flag = arg
    } else {
      name = arg
    }
  }
  if streamp(stream_or_filename) {
    read_struct_from_stream(stream_or_filename, sep_ch_flag, if name.truthy() {
      name
    } else {
      d_gensym(x=Str("data"))
    })
  } else {
    let file_name = require_string(stream_or_filename)
    share_numericalio__with_input_file(file_name, q_text, in_ => if in_.truthy() {
      read_struct_from_stream(in_, sep_ch_flag, if name.truthy() {
        name
      } else {
        read_struct_default_name(file_name)
      })
    } else {
      merror(Str("read_struct: no such file `~a'"), list1(file_name))
    })
  }
}

///|
/// Is ARG a separator flag, and not the name to give the structure?
fn read_struct_separator_flag_p(arg : Value) -> Value raise {
  lbool(
    stringp(arg) ||
    [q_d_space, q_d_tab, q_d_comma, q_d_pipe, q_d_semicolon, q_d_csv]
    .iter()
    .any(f => eq(f, arg)),
  )
}

///|
/// A name of its own for the structure read from FILE-NAME.
fn read_struct_default_name(file_name : Value) -> Value raise {
  d_gensym(x=read_struct_name_stem(file_name))
}

///|
/// The name of the file, with every character that cannot stand in a
/// Maxima name replaced by an underscore.
fn read_struct_name_stem(file_name : Value) -> Value raise {
  // (pathname-name (pathname file-name)): the last path component without
  // its type.
  let path = match file_name {
    Str(s) => s
    _ => ""
  }
  let mut base = match path.rev_find("/") {
    Some(i) => path.substring(start=i + 1)
    None => path
  }
  match base.rev_find(".") {
    Some(i) if i > 0 => base = base.substring(end=i)
    _ => ()
  }
  let cs = string_chars(base).map(c => if c.is_ascii_alphabetic() ||
    c.is_ascii_digit() ||
    c == '_' {
    c
  } else {
    '_'
  })
  let cs = if cs.length() > 32 { cs[0:32].to_array() } else { cs }
  if cs.length() == 0 || cs[0].is_ascii_digit() {
    Str("_" + chars_to_string(cs))
  } else {
    Str(chars_to_string(cs))
  }
}

///|
/// The name FIELD stands for, as a symbol.
fn read_struct_field_name(field : Value) -> Value raise {
  if symbolp(field) && field.truthy() {
    field
  } else if stringp(field) {
    intern_invert_case(Str("$" + lstring(field)))
  } else {
    merror(
      Str(
        "read_struct: ~M does not name a field; expected a symbol or a string.",
      ),
      list1(field),
    )
  }
}

///|
/// The first name FIELDS holds more than once, or NIL if it holds none.
fn read_struct_repeated_name(fields : Value) -> Value raise {
  let mut rest = fields
  while rest is Cons(_) {
    if member(car(rest), cdr(rest)).truthy() {
      return car(rest)
    }
    rest = cdr(rest)
  }
  Nil
}

///|
fn read_struct_from_stream(
  in_ : Value,
  sep_ch_flag : Value,
  name : Value,
) -> Value raise {
  let sep_ch = get_input_sep_ch(sep_ch_flag, in_)
  let header = match read_line(stream=in_) {
    Some(h) => h
    None =>
      return merror(
        Str(
          "read_struct: the source is empty; expected a first line naming the fields.",
        ),
        Nil,
      )
  }
  let fields = mapcar(
    f => read_struct_field_name(f),
    cdr(make_mlist_from_string(Str(header), sep_ch)),
  )
  let n = length(fields)
  let mut columns = make_list_(n)
  let mut line_number = 1
  if n == 0 {
    merror(Str("read_struct: the first line of the source names no fields."), Nil)
    |> ignore
  }
  let repeated = read_struct_repeated_name(fields)
  if repeated.truthy() {
    merror(
      Str("read_struct: the first line of the source names ~M twice."),
      list1(repeated),
    )
    |> ignore
  }
  while true {
    let line = match read_line(stream=in_) {
      Some(l) => l
      None => break
    }
    line_number = line_number + 1
    let values = cdr(make_mlist_from_string(Str(line), sep_ch))
    // An empty line is no row, as it is none to READ_MATRIX.
    if values.truthy() {
      if length(values) != n {
        merror(
          Str(
            "read_struct: line ~M holds ~M values, but ~M fields were named.",
          ),
          list([int(line_number), int(length(values)), int(n)]),
        )
        |> ignore
      }
      // Each value is pushed onto its column.
      let acc = Collector::new()
      let mut vs = values
      let mut cs = columns
      while vs is Cons(_) && cs is Cons(_) {
        acc.add(cons(car(vs), car(cs)))
        vs = cdr(vs)
        cs = cdr(cs)
      }
      columns = acc.result()
    }
  }
  defstruct1(cons(list1(name), fields)) |> ignore
  cons(
    list1(name),
    mapcar(column => cons(list1(q_mlist), nreverse(column)), columns),
  )
}

///|
/// (make-list n)
fn make_list_(n : Int) -> Value {
  let mut l : Value = Nil
  for _ in 0..<n {
    l = cons(Nil, l)
  }
  l
}

///|
fn make_mlist_from_string(s : Value, sep_ch : Value) -> Value raise {
  let v = fast_mlist_from_string(s, sep_ch)
  if v.truthy() {
    v
  } else {
    slow_mlist_from_string(s, sep_ch)
  }
}

// A line that holds nothing but numbers is scanned by the fast path below;
// anything else is read by SLOW-MLIST-FROM-STRING with the Maxima scanner.

///|
fn fast_mlist_from_string(s : Value, sep_ch : Value) -> Value raise {
  // The scan below reads digits and an exponent marker, which is what they
  // mean in base ten. (*read-base* is always 10 in the port.)
  let separator = fast_separator_char(sep_ch)
  if separator is Nil {
    Nil
  } else if eql(separator, Char(' ')) {
    fast_whitespace_fields(s)
  } else {
    fast_separated_fields(s, separator)
  }
}

///|
/// The character GET-INPUT-SEP-CH's separator stands for, or NIL for one this
/// does not read.
fn fast_separator_char(sep_ch : Value) -> Value raise {
  if eql(sep_ch, Char(' ')) {
    Char(' ')
  } else if eq(sep_ch, sym("$,")) {
    Char(',')
  } else if eq(sep_ch, sym("$|")) {
    Char('|')
  } else if eq(sep_ch, sym("$;")) {
    Char(';')
  } else {
    Nil
  }
}

///|
fn share_numericalio__whitespacep(c : Char) -> Bool raise {
  member(Char(c), symval(q_ear_whitespace_chars)).truthy()
}

///|
/// The whitespace separated numbers of S as a Maxima list, or NIL if S holds
/// anything else.
fn fast_whitespace_fields(s : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  let n = cs.length()
  let mut i = 0
  let fields = Collector::new()
  while true {
    while i < n && share_numericalio__whitespacep(cs[i]) {
      i = i + 1
    }
    if i >= n {
      return cons(list1(q_mlist), fields.result())
    }
    let start = i
    while i < n && !share_numericalio__whitespacep(cs[i]) {
      i = i + 1
    }
    let value = scan_plain_number(s, int(start), int(i))
    if value is Nil {
      return Nil
    }
    fields.add(value)
  }
  Nil
}

///|
/// The SEPARATOR separated numbers of S as a Maxima list, or NIL if S holds
/// anything else. An empty field stands for no value.
fn fast_separated_fields(s : Value, separator : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  let sepc = match separator {
    Char(c) => c
    _ => ' '
  }
  let n = cs.length()
  let mut start = 0
  let fields = Collector::new()
  let mut found = false
  while true {
    let mut stop : Int? = None
    for k in start..<n {
      if cs[k] == sepc {
        stop = Some(k)
        break
      }
    }
    let end = match stop {
      Some(k) => k
      None => n
    }
    if fast_blank_p(s, int(start), int(end)).truthy() {
      fields.add(Nil)
    } else {
      let value = scan_plain_number(
        s,
        fast_skip_blanks(s, int(start), int(end)),
        fast_back_over_blanks(s, int(start), int(end)),
      )
      if value is Nil {
        return Nil
      }
      found = true
      fields.add(value)
    }
    match stop {
      Some(k) => {
        found = true
        start = k + 1
      }
      None =>
        // A line with neither a number nor a separator is empty.
        return if found {
          cons(list1(q_mlist), fields.result())
        } else {
          list1(list1(q_mlist))
        }
    }
  }
  Nil
}

///|
fn fast_blank_p(s : Value, start : Value, end : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  for i in to_int(start)..<to_int(end) {
    if !share_numericalio__whitespacep(cs[i]) {
      return Nil
    }
  }
  t
}

///|
fn fast_skip_blanks(s : Value, start : Value, end : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  let mut i = to_int(start)
  let e = to_int(end)
  while !(i >= e || !share_numericalio__whitespacep(cs[i])) {
    i = i + 1
  }
  int(i)
}

///|
fn fast_back_over_blanks(s : Value, start : Value, end : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  let mut i = to_int(end)
  let st = to_int(start)
  while !(i <= st || !share_numericalio__whitespacep(cs[i - 1])) {
    i = i - 1
  }
  int(i)
}

///|
/// The number S spells between START and END, read as MAKE-NUMBER would read
/// it, or NIL if what stands there is not a number this handles (a bigfloat
/// is not).
fn scan_plain_number(s : Value, start : Value, end : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  let start = to_int(start)
  let end = to_int(end)
  let mut i = start
  let mut digits = false
  let mut marker_index : Int? = None
  if i < end && (cs[i] == '+' || cs[i] == '-') {
    i = i + 1
  }
  while i < end && cs[i].is_ascii_digit() {
    digits = true
    i = i + 1
  }
  if i < end && cs[i] == '.' {
    i = i + 1
    while i < end && cs[i].is_ascii_digit() {
      digits = true
      i = i + 1
    }
  }
  if !digits {
    return Nil
  }
  if i < end {
    let marker = cs[i]
    marker_index = Some(i)
    if !"eEfFsSdDlL".contains_char(marker) {
      return Nil
    }
    i = i + 1
    if i < end && (cs[i] == '+' || cs[i] == '-') {
      i = i + 1
    }
    let mut exponent_digits = false
    while i < end && cs[i].is_ascii_digit() {
      exponent_digits = true
      i = i + 1
    }
    if !exponent_digits {
      return Nil
    }
  }
  if i != end {
    return Nil
  }
  let text = cs[start:end].to_array()
  // MAKE-NUMBER puts +FLONUM-EXPONENT-MARKER+ in place of the exponent
  // marker, so that a number written with any marker is read as a flonum.
  match marker_index {
    Some(k) =>
      text[k - start] = match symval(q_n_plusflonum_exponent_marker_plus) {
        Char(c) => c
        _ => 'D'
      }
    None => ()
  }
  match parse_number_token(chars_to_string(text)) {
    Some(v) => v
    None => Nil
  }
}

///|
fn slow_mlist_from_string(s : Value, sep_ch : Value) -> Value raise {
  // scan-one-token-g isn't happy with symbol at end of string.
  let s = lstring(s) + " "
  with_special(q_ear_parse_stream, make_string_input_stream(s), () => {
    let mut l : Value = Nil
    let mut ll : Value = Nil
    let mut sign : Value = Nil
    let mut found_token : Value = Nil
    let mut found_sep : Value = Nil
    while true {
      let mut token = scan_one_token_g(t, q_eof)
      if eq(token, q_eof) {
        if sign.truthy() {
          format(
            t,
            "numericalio: trailing sign (~S) at end of line; strange, but just eat it.~%",
            [sign],
          )
          |> ignore
        }
        if eql(sep_ch, Char(' ')) {
          return cons(list1(q_mlist), nreverse(ll))
        } else if found_token.truthy() || found_sep.truthy() {
          return cons(list1(q_mlist), nreverse(cons_appropriate_field(ll, l)))
        } else {
          // We reached EOF without encountering a token or a separator;
          // this is an empty line.
          return list1(list1(q_mlist))
        }
      }
      if eq(token, q_d_op_h_) || eq(token, q_d_op_plus) {
        sign = if eq(token, q_d_op_h_) { Fix(-1L) } else { Fix(1L) }
      } else {
        if sign.truthy() {
          token = mul2_star(sign, token)
          sign = Nil
        }
        if eql(sep_ch, Char(' ')) {
          found_token = token
          ll = cons(token, ll)
        } else if eql(token, sep_ch) {
          found_sep = token
          l = cons_appropriate_field(ll, l)
          ll = Nil
        } else {
          found_token = token
          ll = cons(token, ll)
        }
      }
    }
    Nil
  })
}

///|
/// Prefix onto the reversed field list L the field whose tokens are the
/// reversed list LL.
fn cons_appropriate_field(ll : Value, l : Value) -> Value raise {
  if ll is Nil {
    cons(Nil, l)
  } else if cdr(ll) is Nil {
    cons(car(ll), l)
  } else {
    cons(cons(list1(q_mlist), reverse(ll)), l)
  }
}

// ----- begin backwards compatibility stuff ... sigh -----

///|
fn d_read_lisp_array(
  file_name : Value,
  a : Value,
  sep_ch_flag? : Value = Nil,
) -> Value raise {
  d_read_array(file_name, list2(a, sep_ch_flag))
}

///|
fn d_read_maxima_array(
  file_name : Value,
  a : Value,
  sep_ch_flag? : Value = Nil,
) -> Value raise {
  d_read_array(file_name, list2(a, sep_ch_flag))
}

// ---- read one element

///|
/// The closure state of RESET-FOR-PARSE-NEXT-ELEMENT / PARSE-NEXT-ELEMENT.
let share_numericalio__prev_token_sep_ch : Ref[Value] = Ref::new(Nil)

///|
let share_numericalio__sign : Ref[Value] = Ref::new(Nil)

///|
let share_numericalio__start_of_line : Ref[Value] = Ref::new(Nil)

///|
fn reset_for_parse_next_element() -> Value raise {
  share_numericalio__prev_token_sep_ch.val = Nil
  share_numericalio__sign.val = Fix(1L)
  share_numericalio__start_of_line.val = t
  t
}

///|
fn parse_next_element(in_ : Value, sep_ch : Value) -> Value raise {
  // Treat newline as a token, so leading/trailing separators can be
  // detected, when separator is anything other than a space.
  with_specials(
    [
      (q_ear_parse_stream, in_),
      (
        q_ear_whitespace_chars,
        if eql(sep_ch, Char(' ')) {
          symval(q_ear_whitespace_chars)
        } else {
          symval(q_whitespace_sans_newline)
        },
      ),
    ],
    () => {
      while true {
        let token = scan_one_token_g(t, q_eof)
        if eq(token, symval(q_newline_symbol)) {
          share_numericalio__start_of_line.val = t
          if share_numericalio__prev_token_sep_ch.val.truthy() {
            share_numericalio__prev_token_sep_ch.val = Nil
            return Nil
          }
        } else if eq(token, q_eof) {
          if share_numericalio__prev_token_sep_ch.val.truthy() {
            share_numericalio__prev_token_sep_ch.val = Nil
            return Nil
          }
          return q_eof
        } else if eql(token, sep_ch) && !eql(sep_ch, Char(' ')) {
          // We have a separator token. If the preceding token was also a
          // separator, or we're at the start of a line, return NIL.
          if share_numericalio__prev_token_sep_ch.val.truthy() ||
            share_numericalio__start_of_line.val.truthy() {
            share_numericalio__start_of_line.val = Nil
            return Nil
          }
          share_numericalio__prev_token_sep_ch.val = token
        } else {
          // ((prog nil (setq start-of-line nil))) and
          // ((prog nil (setq prev-token-sep-ch nil))) both fall through.
          share_numericalio__start_of_line.val = Nil
          share_numericalio__prev_token_sep_ch.val = Nil
          if eq(token, q_d_op_h_) || eq(token, q_d_op_plus) {
            share_numericalio__sign.val = num_mul(
              share_numericalio__sign.val,
              if eq(token, q_d_op_h_) {
                Fix(-1L)
              } else {
                Fix(1L)
              },
            )
          } else {
            let return_value = mul2_star(share_numericalio__sign.val, token)
            share_numericalio__sign.val = Fix(1L)
            return return_value
          }
        }
      }
      Nil
    },
  )
}

// -------------------- write functions -------------------

///|
fn open_file_appropriately(file_name : Value, mode : Value) -> Value raise {
  let fa = symval(q_d_file_output_append)
  share_numericalio__open_output(
    lstring(file_name),
    !eq(mode, q_text),
    eq(fa, q_d_true) || eq(fa, t),
  )
}

///|
fn d_write_data(
  x : Value,
  stream_or_filename : Value,
  sep_ch_flag? : Value = Nil,
) -> Value raise {
  write_data(x, stream_or_filename, sep_ch_flag, q_text)
}

///|
fn d_write_binary_data(x : Value, stream_or_filename : Value) -> Value raise {
  write_data(x, stream_or_filename, Nil, q_binary)
}

///|
fn write_data(
  x : Value,
  stream_or_filename : Value,
  sep_ch_flag : Value,
  mode : Value,
) -> Value raise {
  let out = if streamp(stream_or_filename) {
    stream_or_filename
  } else {
    open_file_appropriately(require_string(stream_or_filename), mode)
  }
  if d_matrixp(x).truthy() {
    write_matrix(x, out, sep_ch_flag, mode) |> ignore
  } else if arrayp(x) {
    write_lisp_array(x, out, sep_ch_flag, mode) |> ignore
  } else if mget(x, q_array).truthy() {
    write_maxima_array(x, out, sep_ch_flag, mode) |> ignore
  } else if mget(x, q_hashar).truthy() {
    write_hashed_array(x, out, sep_ch_flag, mode) |> ignore
  } else if d_listp(x).truthy() {
    write_list(x, out, sep_ch_flag, mode) |> ignore
  } else {
    merror(
      Str("write_data: don't know what to do with a ~M"),
      list1(share_numericalio__type_of(x)),
    )
    |> ignore
  }
  if streamp(stream_or_filename) {
    // (finish-output out): a file stream's output reaches its file.
    match share_stringproc__file_of(out) {
      Some(f) => share_stringproc__write_out(f)
      None => finish_output(stream=out)
    }
  } else {
    share_numericalio__close(out)
  }
  q_d_done
}

///|
fn write_matrix(
  m : Value,
  out : Value,
  sep_ch_flag : Value,
  mode : Value,
) -> Value raise {
  let sep_ch = get_output_sep_ch(sep_ch_flag, out)
  mapcar(x => write_list_lowlevel(cdr(x), out, sep_ch, mode), cdr(m))
}

///|
fn write_lisp_array(
  a : Value,
  out : Value,
  sep_ch_flag : Value,
  mode : Value,
) -> Value raise {
  let sep_ch = get_output_sep_ch(sep_ch_flag, out)
  let d = array_dimensions(a)
  write_lisp_array_helper(a, d, Nil, out, sep_ch, mode)
}

///|
fn write_lisp_array_helper(
  a : Value,
  d : Value,
  indices : Value,
  out : Value,
  sep_ch : Value,
  mode : Value,
) -> Value raise {
  if length(d) == 1 {
    let mut l : Value = Nil
    for i in 0..<to_int(car(d)) {
      let idx = reverse(cons(int(i), indices))
      let ix : Array[Int] = []
      for v in idx.iter() {
        ix.push(to_int(v))
      }
      let x = aref(a, ix)
      l = cons(x, l)
    }
    write_list_lowlevel(reverse(l), out, sep_ch, mode)
  } else {
    for i in 0..<to_int(car(d)) {
      write_lisp_array_helper(a, cdr(d), cons(int(i), indices), out, sep_ch, mode)
      |> ignore
      if eq(mode, q_text) && length(d) > 2 {
        terpri(stream=out)
      }
    }
    Nil
  }
}

///|
fn write_maxima_array(
  a : Value,
  out : Value,
  sep_ch_flag : Value,
  mode : Value,
) -> Value raise {
  write_lisp_array(symbol_array(mget(a, q_array)), out, sep_ch_flag, mode)
}

///|
fn write_hashed_array(
  a : Value,
  out : Value,
  sep_ch_flag : Value,
  mode : Value,
) -> Value raise {
  let mut keys = cdddr(meval(list2(list1(q_d_arrayinfo), a)))
  let sep_ch = get_output_sep_ch(sep_ch_flag, out)
  while keys.truthy() {
    let mut l = d_arrayapply(a, car(keys))
    if listp(l) {
      l = cdr(l)
    } else {
      l = list1(l)
    }
    let key = car(keys)
    keys = cdr(keys)
    write_list_lowlevel(append(cdr(key), l), out, sep_ch, mode) |> ignore
  }
  Nil
}

///|
fn write_list(l : Value, out : Value, sep_ch_flag : Value, mode : Value) -> Value raise {
  let sep_ch = get_output_sep_ch(sep_ch_flag, out)
  write_list_lowlevel(cdr(l), out, sep_ch, mode)
}

///|
fn write_list_lowlevel(
  l : Value,
  out : Value,
  sep_ch : Value,
  mode : Value,
) -> Value raise {
  let sep_ch = if symbolp(sep_ch) { cadr(exploden(sep_ch)) } else { sep_ch }
  if l is Nil {
    terpri(stream=out)
    return Nil
  }
  let mut l = l
  while l.truthy() {
    let e = car(l)
    l = cdr(l)
    if d_listp(e).truthy() {
      write_list_lowlevel(cdr(e), out, sep_ch, mode) |> ignore
    } else if eq(mode, q_text) {
      with_special(q_d_lispdisp, t, () => mgrind(e, out)) |> ignore
      if l is Nil {
        terpri(stream=out)
      } else {
        match sep_ch {
          Char(c) => write_char(c, stream=out)
          _ => ()
        }
      }
    } else if eq(mode, q_binary) {
      if d_numberp(e).truthy() {
        write_float(d_float(e), out) |> ignore
      } else {
        merror(
          Str("write_data: encountered non-numeric data in binary output"),
          Nil,
        )
        |> ignore
      }
    } else {
      merror(Str("write_data: unrecognized mode"), Nil) |> ignore
    }
  }
  Nil
}

///|
fn get_input_sep_ch(sep_ch_flag : Value, my_stream : Value) -> Value raise {
  if eq(sep_ch_flag, q_d_tab) {
    format(
      t,
      "numericalio: separator flag ``tab'' not recognized for input; assume ``space'' instead.~%",
      [],
    )
    |> ignore
    Char(' ')
  } else {
    get_output_sep_ch(sep_ch_flag, my_stream)
  }
}

///|
fn get_output_sep_ch(sep_ch_flag : Value, my_stream : Value) -> Value raise {
  if eq(sep_ch_flag, q_d_space) {
    Char(' ')
  } else if eq(sep_ch_flag, q_d_tab) {
    Char('\t')
  } else if eq(sep_ch_flag, q_d_comma) || eq(sep_ch_flag, q_d_csv) {
    // '$csv is backwards compatibility ... sigh
    sym("$,")
  } else if eq(sep_ch_flag, q_d_pipe) {
    sym("$|")
  } else if eq(sep_ch_flag, q_d_semicolon) {
    sym("$;")
  } else if stringp(sep_ch_flag) {
    let cs = string_chars(lstring(sep_ch_flag))
    if cs.length() != 1 {
      format(t, "numericalio: unrecognized separator; assume ``space''.~%", [])
      |> ignore
      Char(' ')
    } else {
      match cs[0] {
        ' ' => Char(' ')
        '\t' => Char('\t')
        ',' => sym("$,")
        '|' => sym("$|")
        ';' => sym("$;")
        c => {
          format(
            t,
            "numericalio: separator flag ~S not recognized; assume ``space''.~%",
            [Char(c)],
          )
          |> ignore
          Char(' ')
        }
      }
    }
  } else if sep_ch_flag is Nil {
    // (equal (pathname-type (truename my-stream)) "csv")
    match my_stream {
      Stream(st) if st.name.has_suffix(".csv") => sym("$,")
      _ => Char(' ')
    }
  } else {
    format(
      t,
      "numericalio: separator flag ~S not recognized; assume ``space''.~%",
      [stripdollar(sep_ch_flag)],
    )
    |> ignore
    Char(' ')
  }
}

///|
fn require_string(s : Value) -> Value raise {
  if stringp(s) {
    s
  } else {
    merror(
      Str("numericalio: expected a string, instead found a ~:M"),
      list1(share_numericalio__type_of(s)),
    )
  }
}

///|
fn init_share_numericalio() -> Unit raise {
  // (defvar newline-symbol (intern (coerce '(#\$ #\newline) 'string)))
  if !boundp(q_newline_symbol) {
    set(q_newline_symbol, sym("$\n")) |> ignore
  }
  // (defvar whitespace-sans-newline (remove #\newline *whitespace-chars*))
  if !boundp(q_whitespace_sans_newline) {
    set(
      q_whitespace_sans_newline,
      remove(Char('\n'), symval(q_ear_whitespace_chars)),
    )
    |> ignore
  }
}
