// Port of share/contrib/state/readfile.lisp (Dan Stanger, 1999): low level
// input for state.mac -- read a circuit description file, one element per
// line: `<type><name> <from> <to> [<expr>]`.

///|
/// *circuit-elements*: orders the elements for the proper tree algorithm.
let share_readfile__circuit_elements : Array[(Char, Value)] = [
  ('1', q_d_unknown),
  ('V', q_d_vsource),
  ('C', sym("$capacitor")),
  ('R', sym("$resistor")),
  ('L', sym("$inductor")),
  ('I', sym("$isource")),
]

///|
/// *circuit-elements-tree*: orders the tree elements for the state equation.
let share_readfile__circuit_elements_tree : Array[Value] = [
  q_d_unknown,
  sym("$capacitor"),
  sym("$resistor"),
  q_d_vsource,
]

///|
/// *circuit-elements-link*: orders the link elements for the state equation.
let share_readfile__circuit_elements_link : Array[Value] = [
  q_d_unknown,
  sym("$inductor"),
  sym("$resistor"),
  sym("$isource"),
]

///|
fn process_type(s : Value) -> Value raise {
  // the CL symbol-name of the port symbol
  let sn = invert_case(symbol_name(s))
  let c = sn.get_char(0).unwrap()
  for e in share_readfile__circuit_elements {
    if e.0 == c {
      return e.1
    }
  }
  q_d_unknown
}

///|
fn share_readfile__get_element_index(e : Value) -> Value raise {
  for i, x in share_readfile__circuit_elements {
    if eql(x.1, e) {
      return int(i)
    }
  }
  raise LispError::SimpleError("invalid value in getelementindex")
}

///|
fn share_readfile__get_tree_element_index(e : Value) -> Value raise {
  for i, x in share_readfile__circuit_elements_tree {
    if eql(x, e) {
      return int(i)
    }
  }
  raise LispError::SimpleError("invalid value in gettreeelementindex")
}

///|
fn share_readfile__get_link_element_index(e : Value) -> Value raise {
  for i, x in share_readfile__circuit_elements_link {
    if eql(x, e) {
      return int(i)
    }
  }
  raise LispError::SimpleError("invalid value in getlinkelementindex")
}

///|
fn share_readfile__whitespace(c : Char) -> Bool {
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0C'
}

///|
/// (read st) on a string stream positioned at `pos`, for the simple tokens
/// of a circuit file (symbols and integers): returns the object and the new
/// position (the delimiting whitespace character is consumed, as CL READ
/// does).
fn share_readfile__read_token(s : String, pos : Int) -> (Value, Int) raise {
  let chars = s.to_array()
  let n = chars.length()
  let mut i = pos
  while i < n && share_readfile__whitespace(chars[i]) {
    i = i + 1
  }
  if i >= n {
    raise LispError::SimpleError("end of file on string input stream")
  }
  let sb = StringBuilder::new()
  while i < n && !share_readfile__whitespace(chars[i]) {
    sb.write_char(chars[i])
    i = i + 1
  }
  if i < n {
    i = i + 1
  }
  let tok = sb.to_string()
  let v : Value = match parse_integer(tok) {
    Some(x) => x
    // an unescaped token is upcased by the CL reader
    None => sym(invert_case(string_upcase(tok)))
  }
  (v, i)
}

///|
fn process_line(l : Value) -> Value raise {
  let s = lstring(l)
  let (ty, p1) = share_readfile__read_token(s, 0)
  let (from, p2) = share_readfile__read_token(s, p1)
  let (to, p3) = share_readfile__read_token(s, p2)
  let chars = s.to_array()
  // (read-line st nil nil): nil at end of input
  let ex : Value = if p3 >= chars.length() {
    Nil
  } else {
    Str(String::from_array(chars[p3:].to_array()))
  }
  let ty_name = invert_case(symbol_name(ty))
  list([
    list1(q_mlist),
    intern_invert_case(Str("$" + ty_name)),
    process_type(ty),
    from,
    to,
    if ex.truthy() {
      d_eval_string(intern_invert_case(Str("&" + lstring(ex))))
    } else {
      Nil
    },
  ])
}

///|
fn share_readfile__readfile(filename : Value) -> Value raise {
  let mut a = list1(list1(q_mlist))
  let text = read_file(lstring(print_invert_case(stripdollar(filename))))
  let lines = text.split("\n").map(x => x.to_string()).to_array()
  // a final newline does not start another line
  if lines.length() > 0 && lines[lines.length() - 1] == "" {
    lines.pop() |> ignore
  }
  for line in lines {
    a = d_cons(process_line(Str(line)), a)
  }
  a
}

///|
fn init_share_readfile() -> Unit raise {
  // DEFMTRFUN definitions: Lisp functions named by the Maxima symbols
  defun(
    q_d_get_ce_lement_ci_ndex,
    args => share_readfile__get_element_index(arg(args, 0)),
    name="$getElementIndex",
  )
  defun(
    q_d_get_ct_ree_ce_lement_ci_ndex,
    args => share_readfile__get_tree_element_index(arg(args, 0)),
    name="$getTreeElementIndex",
  )
  defun(
    q_d_get_cl_ink_ce_lement_ci_ndex,
    args => share_readfile__get_link_element_index(arg(args, 0)),
    name="$getLinkElementIndex",
  )
  defun(
    q_d_readfile,
    args => share_readfile__readfile(arg(args, 0)),
    name="$readfile",
  )
}
