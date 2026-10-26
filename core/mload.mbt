// Port of src/mload.lisp: load, batchload, batch, demo, file_search, and
// the test-suite driver (test-batch, run_testsuite).
//
// CL pathnames are represented by their namestrings; MLOAD__PATH below
// parses a namestring into directory components, name and type the way
// SBCL does, and implements MERGE-PATHNAMES and DIRECTORY (with "*", "?"
// and "**" wildcards) on top of the runtime's file-system primitives.
// File modification times are not available, so the directory cache of
// DIRECTORY-CACHED is never enabled (as if the cache self-test failed).

///|
priv struct Mload__Path {
  abs : Bool
  dirs : Array[String]
  name : String?
  type_ : String?
}

///|
fn mload__parse(s : String) -> Mload__Path {
  let abs = s.has_prefix("/")
  let parts = split_string(s, '/')
  let dirs : Array[String] = []
  let n = parts.length()
  for i = 0; i < n - 1; i = i + 1 {
    if parts[i] != "" {
      dirs.push(parts[i])
    }
  }
  let last = if n > 0 { parts[n - 1] } else { "" }
  if last == "" {
    return { abs, dirs, name: None, type_: None }
  }
  // SBCL: the type is what follows the last dot, unless the dot starts the
  // name.
  let mut dot = -1
  for i = last.length() - 1; i > 0; i = i - 1 {
    if last[i] == '.' {
      dot = i
      break
    }
  }
  if dot > 0 {
    {
      abs,
      dirs,
      name: Some(last.substring(end=dot)),
      type_: Some(last.substring(start=dot + 1)),
    }
  } else {
    { abs, dirs, name: Some(last), type_: None }
  }
}

///|
fn mload__namestring(p : Mload__Path) -> String {
  let sb = StringBuilder::new()
  if p.abs {
    sb.write_string("/")
  }
  for d in p.dirs {
    sb.write_string(d)
    sb.write_string("/")
  }
  match p.name {
    Some(n) => sb.write_string(n)
    None => ()
  }
  match p.type_ {
    Some(t) => {
      sb.write_string(".")
      sb.write_string(t)
    }
    None => ()
  }
  sb.to_string()
}

///|
/// The namestring of a pathname designator (string, symbol, stream).
fn mload__str(x : Value) -> String raise {
  match x {
    Str(s) => s
    Stream(st) => st.name
    Nil => raise LispError::SimpleError("NIL is not a pathname designator")
    _ => princ_to_string(x)
  }
}

///|
/// MERGE-PATHNAMES
fn mload__merge(p : Mload__Path, d : Mload__Path) -> Mload__Path {
  let (abs, dirs) = if p.abs {
    (true, p.dirs)
  } else if p.dirs.length() > 0 {
    (d.abs, d.dirs + p.dirs)
  } else {
    (d.abs, d.dirs)
  }
  {
    abs,
    dirs,
    name: match p.name {
      Some(_) => p.name
      None => d.name
    },
    type_: match p.type_ {
      Some(_) => p.type_
      None => d.type_
    },
  }
}

///|
fn mload__wild_component(s : String) -> Bool {
  s.contains("*") || s.contains("?")
}

///|
fn mload__wild_p(p : Mload__Path) -> Bool {
  p.dirs.iter().any(mload__wild_component) ||
  (match p.name {
    Some(n) => mload__wild_component(n)
    None => false
  }) ||
  (match p.type_ {
    Some(t) => mload__wild_component(t)
    None => false
  })
}

///|
/// Glob-style match of S against PAT ("*" any sequence, "?" one char).
fn mload__glob_match(pat : String, s : String) -> Bool {
  let p = string_chars(pat)
  let c = string_chars(s)
  let np = p.length()
  let nc = c.length()
  // dp over positions
  let mut prev : Array[Bool] = Array::make(nc + 1, false)
  prev[0] = true
  for i = 0; i < np; i = i + 1 {
    let cur : Array[Bool] = Array::make(nc + 1, false)
    if p[i] == '*' {
      let mut any = false
      for j = 0; j <= nc; j = j + 1 {
        any = any || prev[j]
        cur[j] = any
      }
    } else {
      for j = 1; j <= nc; j = j + 1 {
        cur[j] = prev[j - 1] && (p[i] == '?' || p[i] == c[j - 1])
      }
    }
    prev = cur
  }
  prev[nc]
}

///|
fn mload__opt_match(pat : String?, s : String?) -> Bool {
  match (pat, s) {
    (None, None) => true
    (Some(p), Some(v)) => mload__glob_match(p, v)
    (Some(p), None) => p == "*"
    (None, Some(_)) => false
  }
}

///|
fn mload__cwd() -> String {
  match getenv("PWD") {
    Some(d) => d
    None => "."
  }
}

///|
/// The absolute directory namestring for a parsed directory part.
fn mload__dir_string(abs : Bool, dirs : Array[String]) -> String {
  let sb = StringBuilder::new()
  if abs {
    sb.write_string("/")
  } else {
    sb.write_string(mload__cwd())
    sb.write_string("/")
  }
  for d in dirs {
    sb.write_string(d)
    sb.write_string("/")
  }
  sb.to_string()
}

///|
/// Remove "." and ".." components of an absolute namestring (TRUENAME).
fn mload__normalize(s : String) -> String {
  let p = mload__parse(if s.has_prefix("/") { s } else { mload__cwd() + "/" + s })
  let dirs : Array[String] = []
  for d in p.dirs {
    if d == "." {
      ()
    } else if d == ".." {
      dirs.pop() |> ignore
    } else {
      dirs.push(d)
    }
  }
  mload__namestring({ abs: true, dirs, name: p.name, type_: p.type_ })
}

///|
/// Expand the directory part of P (with "*", "?" and "**" components) into
/// existing directories, given as absolute namestrings ending in "/".
/// DESCEND is consulted before descending into a directory because of a
/// wildcard.
fn mload__expand_dirs(
  abs : Bool,
  dirs : Array[String],
  descend : (String) -> Bool raise,
) -> Array[String] raise {
  let out : Array[String] = []
  fn go_(parent : String, i : Int) -> Unit raise {
    if i >= dirs.length() {
      out.push(parent)
      return
    }
    let comp = dirs[i]
    if comp == "**" {
      go_(parent, i + 1)
      for e in mload__sorted_entries(parent) {
        let sub = parent + e + "/"
        if directory_p(sub) && descend(sub) {
          go_(sub, i)
        }
      }
    } else if mload__wild_component(comp) {
      for e in mload__sorted_entries(parent) {
        let sub = parent + e + "/"
        if mload__glob_match(comp, e) && directory_p(sub) && descend(sub) {
          go_(sub, i + 1)
        }
      }
    } else {
      let next = parent + comp + "/"
      if directory_p(next) {
        go_(next, i + 1)
      }
    }
  }

  go_(mload__dir_string(abs, []), 0)
  out
}

///|
fn mload__sorted_entries(dir : String) -> Array[String] {
  let es = list_directory(dir).filter(e => e != "." && e != "..")
  es.sort()
  es
}

///|
/// CL DIRECTORY on a (possibly wild) namestring: the existing files (or,
/// for a pattern without name and type, directories) matching it.
fn mload__directory(
  pattern : String,
  descend? : (String) -> Bool raise = _ => true,
) -> Array[String] raise {
  let p = mload__parse(pattern)
  let dirs = mload__expand_dirs(p.abs, p.dirs, descend)
  let out : Array[String] = []
  for d in dirs {
    match (p.name, p.type_) {
      (None, None) => out.push(d)
      _ =>
        if !(
            mload__opt_wild(p.name) || mload__opt_wild(p.type_)
          ) {
          let f = d + mload__namestring({ abs: false, dirs: [], name: p.name, type_: p.type_ })
          if probe_file(f) {
            out.push(mload__normalize(f))
          }
        } else {
          for e in mload__sorted_entries(d) {
            let f = d + e
            if probe_file(f) {
              let ep = mload__parse(e)
              if mload__opt_match(p.name, ep.name) &&
                mload__opt_match(p.type_, ep.type_) {
                out.push(mload__normalize(f))
              }
            }
          }
        }
    }
  }
  out
}

///|
fn mload__opt_wild(s : String?) -> Bool {
  match s {
    Some(v) => mload__wild_component(v)
    None => false
  }
}

///|
/// COMBINE-PATH (cl-info.lisp): join path components with "/".
fn mload__combine_path(parts : Array[Value]) -> String raise {
  let sb = StringBuilder::new()
  for i = 0; i < parts.length(); i = i + 1 {
    let s = mload__str(parts[i])
    if i > 0 && !sb.to_string().has_suffix("/") {
      sb.write_string("/")
    }
    sb.write_string(s)
  }
  sb.to_string()
}

///|
/// ERRSET (generr.lisp): Some(value), or None if a Lisp error was signalled
/// (re-signalled when the special ERRSET is true).  Maxima errors and
/// control transfers pass through.
fn mload__errset(f : () -> Value raise) -> Value? raise {
  f() catch {
    e if suprv1__control_transfer(e) => raise e
    e if is_maxima_error(e) => raise e
    e => if symval(q_errset).truthy() { raise e } else { None }
  } noraise {
    v => Some(v)
  }
}

///|
fn load_and_tell(filename : Value) -> Value raise {
  // T means this is a lisp-level call, not user-level.
  loadfile(filename, t, symval(q_d_loadprint))
}

///|
fn errset_namestring(x : Value) -> Value raise {
  with_special(q_errset, Nil, () => match mload__errset(() => Str(mload__str(x))) {
    Some(v) => list1(v)
    None => Nil
  })
}

///|
/// Find all the directories in the directory given by PATH.  We do not
/// descend into the subdirectories.
fn get_dirs(path : Value) -> Value raise {
  let ns = mload__str(path)
  let pat = ns + (if ns.has_suffix("/") { "" } else { "/" }) + "*/"
  list(mload__directory(pat).map(s => Str(s)))
}

///|
fn unix_like_basename(path : Value) -> Value raise {
  let mut s = mload__str(path)
  if s.has_suffix("/") {
    s = s.substring(end=s.length() - 1)
  }
  let mut pos = -1
  for i = s.length() - 1; i >= 0; i = i - 1 {
    if s[i] == '/' || s[i] == '\\' {
      pos = i
      break
    }
  }
  Str(s.substring(start=pos + 1))
}

///|
/// A Lisp equivalent of the Unix program dirname.
fn unix_like_dirname(path : Value) -> Value raise {
  let mut s = mload__str(path)
  if s.has_suffix("/") {
    s = s.substring(end=s.length() - 1)
  }
  for i = s.length() - 1; i >= 0; i = i - 1 {
    if s[i] == '/' || s[i] == '\\' {
      return Str(s.substring(end=i))
    }
  }
  Str(".")
}

///|
fn d_filename_merge(file_specs : Value) -> Value raise {
  if file_specs is Nil || cddr(file_specs).truthy() {
    wna_err(q_d_filename_merge) |> ignore
  }
  let specs = mapcar(x => macsyma_namestring_sub(x), file_specs)
  if cdr(specs) is Nil {
    Str(mload__str(car(specs)))
  } else {
    Str(
      mload__namestring(
        mload__merge(
          mload__parse(mload__str(cadr(specs))),
          mload__parse(mload__str(car(specs))),
        ),
      ),
    )
  }
}

///|
fn macsyma_namestring_sub(user_object : Value) -> Value raise {
  if stringp(user_object) {
    return user_object
  }
  let system_object = if atom(user_object) && !symbolp(user_object) {
    user_object
  } else if atom(user_object) {
    Str(princ_to_string(fullstrip1(user_object)))
  } else if d_listp(user_object).truthy() {
    fullstrip(cdr(user_object))
  } else {
    merr("filename_merge: unexpected argument: ~M", [user_object])
  }
  let namestring_try : Value = if consp(system_object) {
    Nil
  } else {
    errset_namestring(system_object)
  }
  if namestring_try.truthy() {
    car(namestring_try)
  } else {
    // know its small now, so print on same line.
    merr("filename_merge: unexpected argument: ~:M", [user_object])
  }
}

///|
/// Returns the truename corresponding to a stream, or nil (for non-file
/// streams).
fn get_stream_truename(stream : Value) -> Value raise {
  match stream {
    Stream(st) =>
      if st.name != "" && st.name != "*terminal-io*" && probe_file(st.name) {
        Str(mload__normalize(st.name))
      } else {
        Nil
      }
    _ => Nil
  }
}

///|
fn mload__open(filename : Value) -> Value raise {
  open_input_file(mload__str(filename))
}

///|
fn d_batchload(filename_or_stream : Value) -> Value raise {
  with_special(q_ear_mread_prompt, Str(""), () => {
    if streamp(filename_or_stream) {
      return batchload_stream(filename_or_stream)
    }
    let filename = d_file_search1(
      filename_or_stream,
      list([list1(q_mlist), q_d_file_search_maxima]),
    )
    if wxmx_file_p(filename).truthy() {
      let in_stream = make_string_input_stream(
        mload__str(wxmx__input_string(filename)),
      )
      batchload_stream(in_stream, truename=Str(mload__str(filename)))
    } else {
      batchload_stream(mload__open(filename))
    }
  })
}

///|
fn batchload_stream(
  in_stream : Value,
  autoloading_p? : Value = Nil,
  truename? : Value = Nil,
) -> Value raise {
  with_specials(
    [(q_d_load_pathname, Nil), (q_noevalargs, Nil), (q_ear_read_base, Fix(10L))],
    () => {
      // A .wxmx worksheet is read from a string stream, which has no
      // truename of its own; TRUENAME names the worksheet it came from.
      let stream_truename = if truename.truthy() {
        truename
      } else {
        get_stream_truename(in_stream)
      }
      let rep = if stream_truename.truthy() {
        set(q_d_load_pathname, Str(mload__str(stream_truename)))
      } else {
        format(Nil, "~A", [in_stream])
      }
      // If we arrived here from autoloading, call MEVAL instead of MEVAL*
      // since MEVAL* is intended to be called from the interpreter top
      // level.
      let autoloading = autoloading_p.truthy()
      if symval(q_d_loadprint).truthy() && !symval(q_ear_maxima_quiet).truthy() {
        suprv1__fmt(t, "~&read and interpret ~A~&", [rep]) |> ignore
      }
      cleanup() |> ignore
      newline(in_stream) |> ignore
      while true {
        let expr = with_special(q_ear_prompt_on_read_hang, Nil, () => mread(
          list([in_stream, Nil]),
        ))
        if !(expr.truthy() && consp(expr)) {
          break
        }
        if autoloading {
          meval(third(expr)) |> ignore
        } else {
          meval_star(third(expr)) |> ignore
        }
      }
      rep
    },
  )
}

///|
/// Returns appropriate error or existing pathname.  The second argument is
/// a maxima list of variables each of which contains a list of paths.
fn d_file_search1(name : Value, search_lists : Value) -> Value raise {
  let lis = d_append(mapcar(s => symval(s), cdr(search_lists)))
  let res = d_file_search(name, paths=lis)
  if res.truthy() {
    res
  } else {
    merr("file_search1: ~M not found in ~A.", [
      name,
      Str(string_trim("[]", lstring(d_sconcat(list1(search_lists))))),
    ])
  }
}

///|
/// This is the generic file loading function.
fn d_load(filename : Value) -> Value raise {
  if stringp(filename) || symbolp(filename) {
    let searched_for = d_file_search1(
      filename,
      list([list1(q_mlist), q_d_file_search_maxima, q_d_file_search_lisp]),
    )
    let type_ = d_file_type(searched_for)
    if eq(type_, q_d_maxima) {
      d_batchload(searched_for) |> ignore
    } else if eq(type_, q_d_lisp) || eq(type_, q_d_object) {
      // do something about handling errors during loading.
      load_and_tell(searched_for) |> ignore
    } else {
      merr("Maxima bug: Unknown file type ~M", [type_]) |> ignore
    }
    searched_for
  } else {
    merr("load: argument must be a string, symbol, or pathname; found: ~M", [
      filename,
    ])
  }
}

///|
fn mload__string_member(typ : Value, l : Value) -> Bool {
  match typ {
    Str(s) =>
      l.iter().any(x => match x {
        Str(y) => y == s
        _ => false
      })
    _ => false
  }
}

///|
fn d_file_type(fil : Value) -> Value raise {
  let typ = d_pathname_type(fil)
  if mload__string_member(typ, cdr(symval(q_d_file_type_lisp))) {
    q_d_lisp
  } else if mload__string_member(typ, cdr(symval(q_d_file_type_maxima))) {
    q_d_maxima
  } else {
    q_d_object
  }
}

///|
fn d_pathname_directory(path : Value) -> Value raise {
  let p = mload__parse(mload__str(path))
  Str(mload__namestring({ abs: p.abs, dirs: p.dirs, name: None, type_: None }))
}

///|
fn d_pathname_name(path : Value) -> Value raise {
  match mload__parse(mload__str(path)).name {
    Some(n) => Str(n)
    None => Nil
  }
}

///|
fn d_pathname_type(path : Value) -> Value raise {
  match mload__parse(mload__str(path)).type_ {
    Some(n) => Str(n)
    None => Nil
  }
}

///|
/// Does FILENAME name a wxMaxima .wxmx worksheet?
fn wxmx_file_p(filename : Value) -> Value raise {
  lbool(
    mload__string_member(
      d_pathname_type(filename),
      cdr(symval(q_d_file_type_wxmx)),
    ),
  )
}

///|
fn generic_autoload(file : Value) -> Value raise {
  if member_equal(file, symval(q_ear_autoloaded_files)).truthy() {
    return Nil
  }
  set(q_ear_autoloaded_files, cons(file, symval(q_ear_autoloaded_files)))
  |> ignore
  let path = mload__str(cdr(file))
  // (pathname-type file) is NIL for a name without a type, which matches
  // none of bin-ext ("" in SBCL), "lisp", "lsp".
  let bin_ext = ""
  let lisp_p = match mload__parse(path).type_ {
    Some(typ) =>
      typ.to_lower() == bin_ext || typ.to_lower() == "lisp" || typ.to_lower() == "lsp"
    None => false
  }
  if lisp_p {
    with_specials([(q_ear_read_base, Fix(10L)), (q_ear_print_base, Fix(10L))], () => suprv1__load_lisp_file(
      path,
    ))
  } else {
    d_load(Str(path))
  }
}

///|
fn d_directory(path : Value) -> Value raise {
  cons(
    list1(q_mlist),
    list(mload__directory(mload__str(d_filename_merge(list1(path)))).map(s => Str(
      s,
    ))),
  )
}

///|
fn d_setup_autoload(filename : Value, functions : Value) -> Value raise {
  let file = d_file_search(filename)
  for func in functions.iter() {
    nonsymchk(func, q_d_setup_autoload) |> ignore
    let func = d_verbify(func)
    putprop(func, file, q_autoload) |> ignore
    add2lnc(func, symval(q_d_props)) |> ignore
  }
  q_d_done
}

///|
/// giving a second argument makes it use demo mode, ie pause after
/// evaluation of each command line
fn d_batch(filename_or_stream : Value, demo? : Value = q_kw_batch) -> Value raise {
  // Try to get rid of testsuite failures on machines that are low on RAM.
  d_garbage_collect() |> ignore
  let possible = list([q_kw_demo, q_kw_batch, q_kw_test])
  let tem = memq(d_mkey(demo), possible)
  let demo = if tem.truthy() {
    car(tem)
  } else {
    suprv1__fmt(
      t,
      "batch: second argument must be 'demo', 'batch' or 'test'; found: ~A, assumed 'batch'~%",
      [demo],
    )
    |> ignore
    demo
  }
  if streamp(filename_or_stream) {
    return batch_stream(filename_or_stream, demo)
  }
  let filename = d_file_search1(
    filename_or_stream,
    if eq(demo, q_kw_demo) {
      list([list1(q_mlist), q_d_file_search_demo])
    } else {
      list([list1(q_mlist), q_d_file_search_maxima])
    },
  )
  if eq(demo, q_kw_test) {
    test_batch(filename, Nil, show_all=t).0
  } else if wxmx_file_p(filename).truthy() {
    let in_stream = make_string_input_stream(
      mload__str(wxmx__input_string(filename)),
    )
    batch_stream(in_stream, demo, truename=Str(mload__str(filename)))
  } else {
    batch_stream(mload__open(filename), demo)
  }
}

///|
fn d_demo(filename : Value) -> Value raise {
  let tem = d_file_search(filename, paths=symval(q_d_file_search_demo))
  if tem is Nil {
    merr("demo: could not find ~M in ~M.", [filename, q_d_file_search_demo])
    |> ignore
  }
  d_batch(tem, demo=q_d_demo)
}

///|
fn batch_stream(in_stream : Value, demo : Value, truename? : Value = Nil) -> Value raise {
  with_specials([(q_d_load_pathname, Nil), (q_ear_read_base, Fix(10L))], () => {
    let stream_truename = if truename.truthy() {
      truename
    } else {
      get_stream_truename(in_stream)
    }
    let rep = if stream_truename.truthy() {
      set(q_d_load_pathname, Str(mload__str(stream_truename)))
    } else {
      format(Nil, "~A", [in_stream])
    }
    let answers = symval(q_d_batch_answers_from_file).truthy()
    let bindings = if answers {
      [
        (q_ear_query_io, make_string_output_stream()),
        (macsys__q_query_input, in_stream),
        (standard_input, in_stream),
      ]
    } else {
      [
        (q_ear_query_io, symval(q_ear_query_io)),
        (macsys__q_query_input, symval(macsys__q_query_input)),
        (standard_input, symval(standard_input)),
      ]
    }
    with_specials(bindings, () => {
      if !symval(q_ear_maxima_quiet).truthy() {
        suprv1__fmt(t, "~%read and interpret ~A~%", [rep]) |> ignore
      }
      catch_tag(q_macsyma_quit, () => continue_(
        input_stream=in_stream,
        batch_or_demo_flag=demo,
      ))
      |> ignore
      set(q_d_linenum, num_add(symval(q_d_linenum), Fix(1L))) |> ignore
      rep
    })
  })
}

///|
/// When either a or b are special float values (NaN or +/-Inf), return true
/// iff a and b are the both NaN or both +Inf or both -Inf.  When a and b are
/// finite, nonzero floats, return true iff
///   |a - b| <= float_approx_equal_tolerance * min(2^n, 2^m)
/// where a = af * 2^m, |af| < 1, and m is an integer (similarly for b).
fn d_float_approx_equal(a : Value, b : Value) -> Value raise {
  let a = if floatp(a) { a } else { d_float(a) }
  let b = if floatp(b) { b } else { d_float(b) }
  match (a, b) {
    (Flo(a), Flo(b)) => {
      // look for NaN
      if a != a {
        return lbool(b != b)
      }
      if b != b {
        return Nil
      }
      // look for Inf
      if a.abs() > most_positive_double_float {
        return lbool(a == b)
      }
      if b.abs() > most_positive_double_float {
        return Nil
      }
      // look for zero
      if a == 0.0 {
        return lbool(b == 0.0)
      }
      if b == 0.0 {
        return Nil
      }
      // look for A = B
      if a == b {
        return t
      }
      // Implement test without involving floating-point arithmetic, to
      // avoid errors which could occur with extreme values.
      let (_, a_expt, a_sign) = decode_float(a)
      let (_, b_expt, b_sign) = decode_float(b)
      let tol = to_double(symval(q_d_float_approx_equal_tolerance))
      if a_sign == b_sign || tol >= 1.0 {
        let (a_b_significand, a_b_expt, _) = integer_decode_float((a - b).abs())
        let (tol_significand, tol_expt, _) = integer_decode_float(tol)
        let m = if a_expt < b_expt { a_expt } else { b_expt }
        lbool(
          a_b_expt < tol_expt + m ||
          (a_b_expt == tol_expt + m && a_b_significand <= tol_significand),
        )
      } else {
        Nil
      }
    }
    _ => Nil
  }
}

///|
/// Big float version of float_approx_equal.  The tolerance is 32 / 2^fpprec.
fn d_bfloat_approx_equal(a : Value, b : Value) -> Value raise {
  let a = if d_bfloatp(a).truthy() { a } else { d_bfloat(a) }
  let b = if d_bfloatp(b).truthy() { b } else { d_bfloat(b) }
  if !(d_bfloatp(a).truthy() && d_bfloatp(b).truthy()) {
    return Nil
  }
  let bits = num_min(third(first(a)), third(first(b)))
  if bits is Nil {
    return Nil
  }
  let m = num_mul(
    num_mul(Fix(32L), expt(Fix(2L), num_neg(bits))),
    num_min(
      expt(Fix(2L), num_sub(car(last(a)), Fix(1L))),
      expt(Fix(2L), num_sub(car(last(b)), Fix(1L))),
    ),
  )
  let m = if rationalp(m) {
    div(numerator(m), denominator(m))
  } else {
    m
  }
  lbool(eq(t, mgqp(m, take(list1(q_mabs), [sub(a, b)]))))
}

///|
/// The first argument 'f' is the expected result; the second argument 'g'
/// is the output of the test.
fn approx_alike(f : Value, g : Value) -> Value raise {
  if floatp(f) {
    return if floatp(g) { d_float_approx_equal(f, g) } else { Nil }
  }
  if d_bfloatp(f).truthy() {
    return if d_bfloatp(g).truthy() { d_bfloat_approx_equal(f, g) } else { Nil }
  }
  if d_taylorp(g).truthy() {
    return approx_alike(Fix(0L), sub(ratdisrep(f), ratdisrep(g)))
  }
  if stringp(f) {
    return lbool(stringp(g) && lstring(f) == lstring(g))
  }
  if arrayp(f) {
    return if arrayp(g) && equal(array_dimensions(f), array_dimensions(g)) {
      approx_alike(d_listarray(f), d_listarray(g))
    } else {
      Nil
    }
  }
  if hash_table_p(f) {
    return if hash_table_p(g) {
      approx_alike(d_listarray(f), d_listarray(g))
    } else {
      Nil
    }
  }
  if atom(f) {
    return lbool(atom(g) && equal(f, g))
  }
  if op_equalp(f, list1(q_lambda)).truthy() {
    return if op_equalp(g, list1(q_lambda)).truthy() {
      approx_alike_list(
        mapcar(s => simplifya(s, Nil), margs(f)),
        mapcar(s => simplifya(s, Nil), margs(g)),
      )
    } else {
      Nil
    }
  }
  if d_ratp(f).truthy() {
    return if d_ratp(g).truthy() {
      approx_alike(ratdisrep(f), ratdisrep(g))
    } else {
      Nil
    }
  }
  // maybe we don't want this.
  if op_equalp(f, list1(q_mquote)).truthy() {
    return approx_alike(second(f), g)
  }
  if consp(f) &&
    consp(car(f)) &&
    consp(g) &&
    consp(car(g)) &&
    (
      approx_alike(mop(f), mop(g)).truthy() ||
      (
        symbolp(mop(f)) &&
        symbolp(mop(g)) &&
        approx_alike(d_nounify(mop(f)), d_nounify(mop(g))).truthy()
      )
    ) &&
    eq(d_subvarp(f), d_subvarp(g)) &&
    approx_alike_list(margs(f), margs(g)).truthy() {
    t
  } else {
    Nil
  }
}

///|
fn approx_alike_list(p : Value, q : Value) -> Value raise {
  let mut p = p
  let mut q = q
  while true {
    if p is Nil {
      return lbool(q is Nil)
    }
    if q is Nil {
      return lbool(p is Nil)
    }
    if !approx_alike(first(p), first(q)).truthy() {
      return Nil
    }
    p = rest(p)
    q = rest(q)
  }
  Nil
}

///|
fn simple_equal_p(f : Value, g : Value) -> Value raise {
  approx_alike(simplifya(f, Nil), simplifya(g, Nil))
}

///|
fn batch_equal_check(expected : Value, result : Value) -> Value raise {
  let answer = catch_tag(q_macsyma_quit, () => simple_equal_p(expected, result)) catch {
    e if is_maxima_error(e) => q_maxima_error
    e => raise e
  }
  if eq(answer, q_maxima_error) {
    Nil
  } else {
    answer
  }
}

///|
fn print_test_batch_problem(
  out : Value,
  filename : Value,
  problem_no : Value,
  problem_lineno : Value,
  input : Value,
) -> Value raise {
  with_special(q_ear_print_base, Fix(10L), () => {
    let center = format_to_string(" ~A: Problem ~A~A ", [
      filename,
      problem_no,
      if problem_lineno.truthy() {
        Str(format_to_string(" (line ~S)", [problem_lineno]))
      } else {
        Str("")
      },
    ])
    let stars_count = to_int(symval(q_d_linel)) - center.length()
    let half_up = to_int(num_ceiling(int(stars_count), b=Fix(2L)).0)
    let half_down = to_int(num_floor(int(stars_count), b=Fix(2L)).0)
    let stars_left = String::make(if half_up > 10 { half_up } else { 10 }, '*')
    let stars_right = String::make(
      if half_down > 10 {
        half_down
      } else {
        10
      },
      '*',
    )
    suprv1__fmt(out, "~%~A~A~A~%", [Str(stars_left), Str(center), Str(stars_right)])
    |> ignore
    suprv1__fmt(out, "~%Input:~%", []) |> ignore
    displa(input)
  })
}

///|
/// Execute the code in FILENAME as a batch file.  If EXPECTED-ERRORS is
/// non-NIL, it is a list of numbers denoting which tests in this file are
/// expected to fail.  Returns four values: the filename, NIL or a Maxima
/// list of test numbers that failed, NIL or a Maxima list of test numbers
/// that were expected to fail but actually passed, and the total number of
/// tests in the file.
fn test_batch(
  filename : Value,
  expected_errors : Value,
  out? : Value,
  show_expected? : Value = Nil,
  show_all? : Value = Nil,
  showtime? : Value = Nil,
) -> (Value, Value, Value, Value) raise {
  let out = match out {
    Some(o) => o
    None => symval(standard_output)
  }
  let show_all = show_all.truthy()
  let show_expected = show_expected.truthy()
  with_specials(
    [
      (q_d_ratprint, Nil),
      (q_ear_mread_prompt, Str("")),
      (q_ear_read_base, Fix(10L)),
      (q_ear_query_io, symval(q_ear_query_io)),
      (macsys__q_query_input, symval(macsys__q_query_input)),
      (standard_input, symval(standard_input)),
    ],
    () => {
      let filename_basename = unix_like_basename(filename)
      let mut error_log : Value = Nil
      let mut error_log_file : String? = None
      let collect = symval(q_ear_collect_errors)
      if collect.truthy() {
        if streamp(collect) {
          error_log = collect
        } else {
          let p = mload__parse(mload__str(filename))
          let f = mload__namestring({
            abs: p.abs,
            dirs: p.dirs,
            name: p.name,
            type_: Some("ERR"),
          })
          error_log = make_string_output_stream()
          error_log_file = Some(f)
        }
        if error_log.truthy() {
          let shown : Value = match error_log_file {
            Some(f) => Str("#<FD-STREAM for \"file " + mload__normalize(f) + "\">")
            None => error_log
          }
          suprv1__fmt(t, "~%batch: write error log to ~a", [shown]) |> ignore
          suprv1__fmt(error_log, "~%/* Maxima error log from tests in ~A", [
            filename,
          ])
          |> ignore
          suprv1__fmt(error_log, " */~2%", []) |> ignore
        }
      }
      let strm = mload__open(filename)
      if symval(q_d_batch_answers_from_file).truthy() {
        set(q_ear_query_io, out) |> ignore
        set(macsys__q_query_input, strm) |> ignore
        set(standard_input, strm) |> ignore
      }
      let start_real_time = macsys__real_time()
      let start_run_time = macsys__run_time()
      let mut num_problems = 0
      let mut i = 0
      let mut all_differences : Value = Nil
      let mut unexpected_pass : Value = Nil
      while true {
        let expr = mread(list([strm, q_eof]))
        if eq(expr, q_eof) {
          break
        }
        num_problems += 1
        let problem_lineinfo = second(first(expr))
        let problem_lineno = if consp(problem_lineinfo) &&
          integerp(first(problem_lineinfo)) {
          num_add(Fix(1L), first(problem_lineinfo))
        } else {
          Nil
        }
        i += 1
        if show_all {
          print_test_batch_problem(
            out,
            filename_basename,
            int(i),
            problem_lineno,
            third(expr),
          )
          |> ignore
        }
        let tmp_output = make_string_output_stream()
        let save_output = symval(standard_output)
        set(standard_output, tmp_output) |> ignore
        let mut test_start_run_time : Value = Fix(0L)
        let mut test_start_real_time : Value = Fix(0L)
        let mut test_end_run_time : Value = Fix(0L)
        let mut test_end_real_time : Value = Fix(0L)
        let result = (fn() -> Value raise {
          test_start_run_time = macsys__run_time()
          test_start_real_time = macsys__real_time()
          let r = with_special(q_d_errormsg, t, () => meval_star(
            list([list1(q_d_errcatch), third(expr)]),
          ))
          let r = if d_emptyp(r).truthy() { q_error_catch } else { second(r) }
          test_end_run_time = macsys__run_time()
          test_end_real_time = macsys__real_time()
          set(q_d_op_pct, r) |> ignore
          r
        })() catch {
          e => {
            set(standard_output, save_output) |> ignore
            raise e
          }
        }
        set(standard_output, save_output) |> ignore
        let next = mread(list([strm, q_eof]))
        if eq(next, q_eof) {
          merr("batch: missing expected result in test script.", []) |> ignore
        }
        let next_result = third(next)
        let correct = batch_equal_check(next_result, result).truthy()
        let expected_error = member(int(i), expected_errors).truthy()
        let pass = correct || expected_error
        if show_all ||
          !pass ||
          (correct && expected_error) ||
          (expected_error && show_expected) {
          if !show_all {
            print_test_batch_problem(
              out,
              filename_basename,
              int(i),
              problem_lineno,
              third(expr),
            )
            |> ignore
          }
          suprv1__fmt(out, "~%~%Result:~%", []) |> ignore
          suprv1__fmt(out, "~a", [Str(get_output_stream_string(tmp_output))])
          |> ignore
          displa(symval(q_d_op_pct)) |> ignore
          if eq(showtime, q_d_all) {
            suprv1__fmt(out, "~%Time:  ~,3F sec (~,3F elapsed)", [
              Flo(
                to_double(num_sub(test_end_run_time, test_start_run_time)) /
                macsys__units_per_second,
              ),
              Flo(
                to_double(num_sub(test_end_real_time, test_start_real_time)) /
                macsys__units_per_second,
              ),
            ])
            |> ignore
          }
        }
        if correct && expected_error {
          unexpected_pass = cons(int(i), unexpected_pass)
          suprv1__fmt(
            t,
            "~%... Which was correct, but was expected to be wrong due to a known bug in~% Maxima or ~A.~%",
            [Str(macsys__lisp_implementation_type())],
          )
          |> ignore
        } else if correct {
          if show_all {
            suprv1__fmt(t, "~%... Which was correct.~%", []) |> ignore
          }
        } else if expected_error {
          if show_all || show_expected {
            suprv1__fmt(
              t,
              "~%This is a known error in Maxima or in ~A. The correct result is:~%",
              [Str(macsys__lisp_implementation_type())],
            )
            |> ignore
            displa(next_result) |> ignore
          }
        } else {
          suprv1__fmt(t, "~%This differed from the expected result:~%", [])
          |> ignore
          all_differences = cons(int(i), all_differences)
          displa(next_result) |> ignore
          if collect.truthy() && error_log.truthy() {
            with_special(q_ear_print_base, Fix(10L), () => suprv1__fmt(
              error_log,
              "/* Problem ~A~A */~%",
              [
                int(i),
                if problem_lineno.truthy() {
                  Str(format_to_string(" (line ~S)", [problem_lineno]))
                } else {
                  Str("")
                },
              ],
            ))
            |> ignore
            mgrind(third(expr), error_log) |> ignore
            list_variable_bindings(third(expr), str=error_log) |> ignore
            suprv1__fmt(error_log, ";~%", []) |> ignore
            suprv1__fmt(error_log, "/* Erroneous Result?:~%", []) |> ignore
            mgrind(result, error_log) |> ignore
            suprv1__fmt(error_log, " */ ", []) |> ignore
            terpri(stream=error_log)
            suprv1__fmt(error_log, "/* Expected result: */~%", []) |> ignore
            mgrind(next_result, error_log) |> ignore
            suprv1__fmt(error_log, ";~%~%", []) |> ignore
          }
        }
      }
      let end_run_time = macsys__run_time()
      let end_real_time = macsys__real_time()
      match error_log_file {
        Some(f) => write_file(f, get_output_stream_string(error_log))
        None => ()
      }
      let n_expected_errors = length(expected_errors)
      let expected_errors_trailer = if n_expected_errors == 0 {
        ""
      } else {
        format_to_string(" (not counting ~a expected errors)", [
          int(n_expected_errors),
        ])
      }
      let time = if showtime.truthy() {
        format_to_string("   using ~,3F seconds (~,3F elapsed).~%", [
          Flo(
            to_double(num_sub(end_run_time, start_run_time)) /
            macsys__units_per_second,
          ),
          Flo(
            to_double(num_sub(end_real_time, start_real_time)) /
            macsys__units_per_second,
          ),
        ])
      } else {
        ""
      }
      let report_unexpected = () => if unexpected_pass.truthy() {
        let (plural, was_were) = if length(unexpected_pass) > 1 {
          ("s", "were")
        } else {
          ("", "was")
        }
        suprv1__fmt(
          t,
          "~%The following ~A problem~A passed but ~A expected to fail: ~A~%",
          [
            int(length(unexpected_pass)),
            Str(plural),
            Str(was_were),
            reverse(unexpected_pass),
          ],
        )
        |> ignore
      }
      if all_differences is Nil {
        suprv1__fmt(t, "~a/~a tests passed~a~%~A", [
          int(num_problems - n_expected_errors),
          int(num_problems - n_expected_errors),
          Str(expected_errors_trailer),
          Str(time),
        ])
        |> ignore
        report_unexpected()
        (
          filename,
          Nil,
          cons(list1(q_mlist), reverse(unexpected_pass)),
          int(num_problems),
        )
      } else {
        suprv1__fmt(t, "~%~a/~a tests passed~a~%~A", [
          int(num_problems - n_expected_errors - length(all_differences)),
          int(num_problems - n_expected_errors),
          Str(expected_errors_trailer),
          Str(time),
        ])
        |> ignore
        let s = if length(all_differences) > 1 { "s" } else { "" }
        suprv1__fmt(t, "~%The following ~A problem~A failed: ~A~%", [
          int(length(all_differences)),
          Str(s),
          reverse(all_differences),
        ])
        |> ignore
        report_unexpected()
        (
          filename,
          cons(list1(q_mlist), reverse(all_differences)),
          cons(list1(q_mlist), reverse(unexpected_pass)),
          int(num_problems),
        )
      }
    },
  )
}

///|
/// to keep track of global values during the error:
fn list_variable_bindings(expr : Value, str? : Value = Nil) -> Value raise {
  let c = Collector::new()
  for v in cdr(d_listofvars(expr)).iter() {
    if member_equal(v, symval(q_d_values)).truthy() {
      let tem = list([list1(q_mequal), v, meval_star(v)])
      c.add(tem)
      if str.truthy() {
        suprv1__fmt(str, ",", []) |> ignore
        mgrind(tem, str) |> ignore
      }
    }
  }
  c.result()
}

///|
/// A file that is being loaded looks for its neighbours the way a C include
/// directive does: TEMPLATES, moved to the directory of the file
/// $LOAD_PATHNAME names, are searched before the search list proper.
fn load_relative_templates(templates : Value) -> Value raise {
  let lp = symval(q_d_load_pathname)
  if lp is Nil {
    return Nil
  }
  let loaded = match lp {
    Str(s) => mload__parse(s)
    _ => return Nil
  }
  // The search list names one directory after another with the same few
  // extensions; beside the loaded file they all collapse into one template
  // per extension.
  let all = mapcar(
    template => {
      let tp = mload__parse(mload__str(template))
      Str(
        mload__namestring({
          abs: loaded.abs,
          dirs: loaded.dirs,
          name: tp.name,
          type_: tp.type_,
        }),
      )
    },
    templates,
  )
  mload__delete_duplicates(all)
}

///|
/// DELETE-DUPLICATES :TEST #'EQUAL -- keeps the last occurrence of each
/// element.
fn mload__delete_duplicates(l : Value) -> Value {
  let c = Collector::new()
  let mut x = l
  while x is Cons({ car: e, cdr: rest }) {
    if !member_equal(e, rest).truthy() {
      c.add(e)
    }
    x = rest
  }
  c.result()
}

///|
fn d_file_search(name : Value, paths? : Value = Nil) -> Value raise {
  let mut name = name
  if symbolp(name) && symbol_name(name).has_prefix("$") {
    name = Str(princ_to_string(name).substring(start=1))
  }
  if symbolp(name) {
    name = Str(symbol_name(name))
  }
  if file_exists_p(name).truthy() {
    return name
  }
  let paths = if paths.truthy() {
    paths
  } else {
    d_append(
      list([
        symval(q_d_file_search_lisp),
        symval(q_d_file_search_maxima),
        symval(q_d_file_search_demo),
      ]),
    )
  }
  atomchk(paths, q_d_file_search, t) |> ignore
  new_file_search(
    Str(mload__str(name)),
    append(load_relative_templates(cdr(paths)), cdr(paths)),
  )
}

///|
/// Returns T if NAME exists and it does not appear to be a directory.
fn file_exists_p(name : Value) -> Value raise {
  match name {
    Str(s) => lbool(s != "" && probe_file(s))
    _ => Nil
  }
}

///|
/// Return T iff VALUE represents a present, meaningful pathname component.
fn pathname_component_present_p(value : Value) -> Value raise {
  match value {
    Nil => Nil
    Str("") => Nil
    _ => if eq(value, q_kw_unspecific) { Nil } else { t }
  }
}

///|
/// Return T iff PATH looks like a directory, i.e. has a non-NIL directory
/// and an absent name and type component.
fn apparently_a_directory_p(path : Value) -> Value raise {
  let p = mload__parse(mload__str(path))
  lbool((p.abs || p.dirs.length() > 0) && p.name is None && p.type_ is None)
}

///|
fn directory_exists_p(path : Value) -> Value raise {
  match mload__errset(() => lbool(directory_p(mload__str(path)))) {
    Some(v) => v
    None => Nil
  }
}

///|
/// Ensure PATH is a directory pathname (name and type both absent).
fn ensure_pathname_as_directory(path : Value) -> Value raise {
  let s = mload__str(path)
  if apparently_a_directory_p(path).truthy() {
    Str(s)
  } else {
    Str(s + "/")
  }
}

///|
/// Return the parent directory of PATH as a directory pathname, or NIL if
/// there is no parent.
fn parent_directory(path : Value) -> Value raise {
  let dir = mload__parse(mload__str(ensure_pathname_as_directory(path)))
  if dir.dirs.length() > 0 && (dir.abs || dir.dirs.length() > 1) {
    let dirs = dir.dirs.copy()
    dirs.pop() |> ignore
    Str(mload__namestring({ abs: dir.abs, dirs, name: None, type_: None }))
  } else {
    Nil
  }
}

///|
/// Return a list of pathnames for the immediate subdirectories of DIR-PATH.
fn immediate_subdirectories(dir_path : Value) -> Value raise {
  let dir = mload__str(ensure_pathname_as_directory(dir_path))
  list(mload__directory(dir + "*/").map(s => Str(s)))
}

///|
fn pathname_versionless_match_p(p1 : Value, p2 : Value) -> Value raise {
  let a = mload__parse(mload__str(p1))
  let b = mload__parse(mload__str(p2))
  if a.abs != b.abs || a.dirs.length() != b.dirs.length() {
    return Nil
  }
  for i = 0; i < a.dirs.length(); i = i + 1 {
    if !(b.dirs[i] == "**" || mload__glob_match(b.dirs[i], a.dirs[i])) {
      return Nil
    }
  }
  lbool(mload__opt_match(b.name, a.name) && mload__opt_match(b.type_, a.type_))
}

///|
/// Return all directories matching the directory part of PATHNAME, which
/// can include wild components.  Before descending into any directory due
/// to a wildcard expansion, DESCENDP is called with that directory.
fn collect_directories(pathname : Value, descendp? : Value) -> Value raise {
  let p = mload__parse(mload__str(pathname))
  let descend = match descendp {
    Some(f) => (d : String) => funcall(f, [Str(d)]).truthy()
    None => (_ : String) => true
  }
  list(mload__expand_dirs(p.abs, p.dirs, descend).map(s => Str(s)))
}

///|
/// Returns the modification time of the file/directory PATH.  The runtime
/// provides no FILE-WRITE-DATE.
fn file_mtime(path : Value) -> Value raise {
  raise LispError::Condition(
    intern("file-error"),
    "file-write-date is not available: " + princ_to_string(path),
    path,
  )
}

///|
fn file_mtime_or_nil(path : Value) -> Value raise {
  match mload__errset(() => file_mtime(path)) {
    Some(v) => v
    None => Nil
  }
}

///|
/// Creates an empty file whose path is combined from PATH.
fn create_empty_file(path : Value) -> Value raise {
  write_file(mload__combine_path(list_to_array(path)), "")
  Nil
}

///|
fn test_directory_cached_dir_base() -> Value raise {
  Str(mload__combine_path([symval(q_ear_maxima_userdir), Str("test-directory-cached"), Str("")]))
}

///|
fn test_directory_cached_dir() -> Value raise {
  Str(
    mload__combine_path([
      test_directory_cached_dir_base(),
      maxima_version1(),
      symval(q_ear_maxima_lispname),
      lisp_implementation_version1(),
    ]),
  )
}

///|
/// Tests whether the directory cache can be used.  Without file
/// modification times the test cannot succeed.
fn test_directory_cached() -> Value raise {
  if file_mtime_or_nil(symval(q_ear_maxima_userdir)) is Nil {
    // The parent directory's mtime cannot be observed either.
    return Nil
  }
  Nil
}

///|
fn check_directory_cached() -> Value raise {
  match mload__errset(() => test_directory_cached()) {
    Some(v) => v
    None => Nil
  }
}

///|
/// Returns a pathname for PATH with :NAME, :TYPE and :VERSION set to NIL.
fn pathname_without_file_components(path : Value) -> Value raise {
  let p = mload__parse(mload__str(path))
  Str(mload__namestring({ abs: p.abs, dirs: p.dirs, name: None, type_: None }))
}

///|
/// Returns T iff P1 is a prefix of P2.
fn pathname_directory_prefix_p(p1 : Value, p2 : Value) -> Value raise {
  let a = mload__parse(mload__str(p1))
  let b = mload__parse(mload__str(p2))
  if a.abs != b.abs || a.dirs.length() > b.dirs.length() {
    return Nil
  }
  for i = 0; i < a.dirs.length(); i = i + 1 {
    if a.dirs[i] != b.dirs[i] {
      return Nil
    }
  }
  t
}

///|
/// Returns a predicate function that can be used for filtering directories
/// to be searched and files to be returned during file search.
fn make_directory_cached_filterp() -> Value raise {
  let ignore_dirs = cdr(symval(q_d_file_search_ignore_dirs))
  let opt = (f : () -> Value raise) => match mload__errset(() => ensure_pathname_as_directory(
      f(),
    )) {
    Some(v) => v
    None => Nil
  }
  let test_dir_base = opt(() => test_directory_cached_dir_base())
  let obj_dir_base = opt(() => maxima_objdir_base())
  let obj_dir = opt(() => symval(q_ear_maxima_objdir))
  lfunc("directory-cached-filterp", args => {
    let path = arg(args, 0)
    let dir = pathname_without_file_components(path)
    let p = mload__parse(mload__str(dir))
    let ignored = p.dirs.iter().any(part => mload__string_member(Str(part), ignore_dirs))
    let pre = (a : Value, b : Value) => a.truthy() &&
      b.truthy() &&
      pathname_directory_prefix_p(a, b).truthy()
    if !ignored &&
      !pre(test_dir_base, dir) &&
      !(pre(obj_dir_base, dir) && !pre(dir, obj_dir) && !pre(obj_dir, dir)) {
      t
    } else {
      if symval(q_ear_debug_directory_cached).truthy() {
        suprv1__fmt(symval(q_ear_debug_io), "directory-cached: ignore \"~A\"~%", [
          path,
        ])
        |> ignore
      }
      Nil
    }
  })
}

///|
/// Behaves like DIRECTORY, but speeds up the search using a cache (which
/// the port never enables, see the file header).
fn directory_cached(path : Value, mtime_cache : Value, filterp? : Value) -> Value raise {
  ignore(mtime_cache)
  if eq(symval(q_d_file_search_cache), q_d_auto) &&
    !(
      eq(symval(q_ear_test_directory_cached_result), t) ||
      symval(q_ear_test_directory_cached_result) is Nil
    ) {
    // Check whether the cache can be used.
    set(q_ear_test_directory_cached_result, check_directory_cached()) |> ignore
  }
  let descend = match filterp {
    Some(f) => (d : String) => funcall(f, [Str(d)]).truthy()
    None => (_ : String) => true
  }
  let files = mload__directory(mload__str(path), descend~)
  let c = Collector::new()
  for f in files {
    if descend(f) {
      c.add(Str(f))
    }
  }
  c.result()
}

///|
/// Search for a file named NAME.  If the file exists, return it.  Otherwise,
/// TEMPLATE is a list of wildcard paths to be searched for the NAME.
fn new_file_search(name : Value, template : Value) -> Value raise {
  let fe = file_exists_p(name)
  if fe.truthy() {
    return fe
  }
  let filename = mload__parse(mload__str(name))
  // Use DELETE-DUPLICATES to avoid searching for the same thing twice when
  // the filename contains a type (e.g. ".mac").
  let merged_pathnames = mload__delete_duplicates(
    mapcar(
      p => Str(mload__namestring(mload__merge(filename, mload__parse(mload__str(p))))),
      template,
    ),
  )
  let mtime_cache = make_hash_table(kind=HashTest::Equal)
  let filterp = make_directory_cached_filterp()
  for path in merged_pathnames.iter() {
    let pathnames = directory_cached(path, mtime_cache, filterp~)
    if symval(q_ear_debug_new_file_search).truthy() {
      suprv1__fmt(symval(q_ear_debug_io), "wildpath ~S~%", [path]) |> ignore
    }
    if pathnames.truthy() {
      // We MUST sort the results in alphabetical order because that's how
      // the old search paths were sorted.
      let arr = list_to_array(pathnames).map(v => lstring(v))
      arr.sort()
      if arr.length() != 1 {
        let sb = StringBuilder::new()
        sb.write_string(
          "More than one file matches.  Selecting the first file from:",
        )
        for i = 0; i < arr.length(); i = i + 1 {
          sb.write_string("\n  " + arr[i])
        }
        sb.write_string("\n")
        mwarning(list1(Str(sb.to_string()))) |> ignore
      }
      return Str(arr[0])
    }
  }
  Nil
}

///|
fn d_printfile(file : Value) -> Value raise {
  let file = d_file_search1(file, list([list1(q_mlist), q_d_file_search_usage]))
  let contents = read_file(mload__str(file))
  write_string(contents)
  file
}

///|
fn disable_some_lisp_warnings() -> Value raise {
  Nil
}

///|
fn enable_some_lisp_warnings() -> Value raise {
  Nil
}

///|
/// Like stripdollar, but less heavy.
fn simple_remove_dollarsign(x : Value) -> Value raise {
  if symbolp(x) {
    Str(princ_to_string(x).substring(start=1))
  } else {
    x
  }
}

///|
fn mload__test_name(x : Value) -> String {
  let v = if listp(x) { second(x) } else { x }
  princ_to_string(v)
}

///|
fn intersect_tests(tests : Value) -> Value raise {
  // If TESTS is non-NIL, we assume it's a Maxima list of (maxima) strings
  // naming the tests we want to run.  They must match the file names in
  // $testsuite_files.  We ignore any items that aren't in $testsuite_files.
  let l = if tests.truthy() {
    let c = Collector::new()
    for tst in mapcar(x => simple_remove_dollarsign(x), cdr(tests)).iter() {
      let name = princ_to_string(tst)
      let m = find_if(
        x => mload__test_name(x) == name,
        cdr(symval(q_d_testsuite_files)),
      )
      if m.truthy() {
        c.add(m)
      }
    }
    c.result()
  } else {
    cdr(symval(q_d_testsuite_files))
  }
  mapcar(x => simple_remove_dollarsign(x), l)
}

///|
fn print_testsuite_summary(
  errs : Value,
  unexpected_pass : Value,
  error_count : Value,
  total_count : Value,
) -> Value raise {
  let problem_summary = (x : Value) => {
    // We want to print all the elements in the list.
    let s = if length(rest(x)) > 1 { "s" } else { "" }
    let sorted = sort_list(copy_list(rest(x)), (a, b) => num_lt(a, b))
    suprv1__fmt(t, "  ~a problem~a:~%    ~a~%", [first(x), Str(s), sorted])
    |> ignore
  }
  if errs is Nil {
    suprv1__fmt(t, "~%~%No unexpected errors found out of ~:d tests.~%", [
      total_count,
    ])
    |> ignore
  } else {
    suprv1__fmt(t, "~%Error summary:~%", []) |> ignore
  }
  if errs.truthy() {
    suprv1__fmt(t, "Error(s) found:~%", []) |> ignore
    for x in reverse(errs).iter() {
      problem_summary(x)
    }
  }
  if unexpected_pass.truthy() {
    suprv1__fmt(t, "Tests that were expected to fail but passed:~%", [])
    |> ignore
    for x in reverse(unexpected_pass).iter() {
      problem_summary(x)
    }
  }
  if errs.truthy() {
    suprv1__fmt(t, "~&~:d test~p failed out of ~:d total tests.~%", [
      error_count, error_count, total_count,
    ])
    |> ignore
  }
  Nil
}

///|
fn validate_given_tests(tests : Value, share_tests_p : Value) -> Value raise {
  // Check the test names and print out some warnings if it doesn't exist,
  // or if it does and is part of the share test suite, but share_tests was
  // not set.
  let names = mapcar(
    x => simple_remove_dollarsign(x),
    if listp(tests) {
      cdr(tests)
    } else {
      list1(tests)
    },
  )
  for tst in names.iter() {
    let name = princ_to_string(tst)
    if !share_tests_p.truthy() &&
      find_if(
        x => mload__test_name(x) == name,
        cdr(symval(q_d_share_testsuite_files)),
      ).truthy() {
      mwarning(list([tst, Str("is a share test, but share_tests was not set")]))
      |> ignore
    } else if !find_if(
        x => mload__test_name(x) == name,
        cdr(symval(q_d_testsuite_files)),
      ).truthy() {
      mwarning(list([Str("Unknown test: "), tst])) |> ignore
    }
  }
  Nil
}

///|
/// Run the testsuite.
fn d_run_testsuite(
  tests? : Value = Nil,
  display_all? : Value = Nil,
  display_known_bugs? : Value = Nil,
  share_tests? : Value = Nil,
  time? : Value = Nil,
  debug_? : Value = Nil,
  answers_from_file? : Value = t,
) -> (Value, Value) raise {
  enable_some_lisp_warnings() |> ignore
  suprv1__fmt(t, "Testsuite run for ~a ~a:~%", [
    Str(macsys__lisp_implementation_type()),
    Str(macsys__lisp_implementation_version()),
  ])
  |> ignore
  let tf = (x : Value) => x is Nil || eq(x, t)
  // Allow only T and NIL for display_known_bugs and display_all
  if !tf(display_known_bugs) {
    merr("run_testsuite: display_known_bugs must be true or false; found: ~M", [
      display_known_bugs,
    ])
    |> ignore
  }
  if !tf(display_all) {
    merr("run_testsuite: display_all must be true or false; found: ~M", [
      display_all,
    ])
    |> ignore
  }
  if !(tf(time) || eq(time, q_d_all)) {
    merr("run_testsuite: time must be true, false, or all; found: ~M", [time])
    |> ignore
  }
  if !(tf(share_tests) || eq(share_tests, q_d_only)) {
    merr("run_testsuite: share_tests must be true, false or only: found ~M", [
      share_tests,
    ])
    |> ignore
  }
  if !tf(answers_from_file) {
    merr(
      "run_testsuite: answers_from_file must be true or false only; found ~M",
      [answers_from_file],
    )
    |> ignore
  }
  set(q_ear_collect_errors, Nil) |> ignore
  let (desired_tests, desired_search_path) = if share_tests is Nil {
    (symval(q_d_testsuite_files), symval(q_d_file_search_tests))
  } else if eq(share_tests, t) {
    // Append the share files and concatenate the search paths for tests and
    // maxima so we can find both sets of tests.
    (
      d_append(
        list([symval(q_d_testsuite_files), symval(q_d_share_testsuite_files)]),
      ),
      cons(
        list1(q_mlist),
        append(
          rest(symval(q_d_file_search_tests)),
          rest(symval(q_d_file_search_maxima)),
        ),
      ),
    )
  } else {
    // Only the share test files
    (symval(q_d_share_testsuite_files), symval(q_d_file_search_maxima))
  }
  let done = with_specials(
    [
      (q_d_testsuite_files, desired_tests),
      (q_d_file_search_tests, desired_search_path),
      (q_d_batch_answers_from_file, answers_from_file),
    ],
    () => {
      let tests_to_run = intersect_tests(
        if consp(tests) {
          tests
        } else if tests.truthy() {
          list([list1(q_mlist), tests])
        } else {
          Nil
        },
      )
      validate_given_tests(tests, share_tests) |> ignore
      if debug_.truthy() {
        with_special(q_d_stringdisp, t, () => {
          mformat(
            list([t, Str("$testsuite_files = ~M~%"), symval(q_d_testsuite_files)]),
          )
          |> ignore
          mformat(
            list([
              t,
              Str("$file_search_tests = ~M~%"),
              symval(q_d_file_search_tests),
            ]),
          )
        })
        |> ignore
      }
      if debug_.truthy() {
        with_special(q_d_stringdisp, t, () => mformat(
          list([t, Str("tests-to-run = ~M~%"), tests_to_run]),
        ))
        |> ignore
      }
      if tests_to_run is Nil {
        mwarning(list1(Str("No tests to run"))) |> ignore
        return q_d_done
      }
      let start_real = macsys__real_time()
      let start_run = macsys__run_time()
      let mut errs : Value = Nil
      let mut unexpected_pass : Value = Nil
      let mut total_count = 0
      let mut error_count = 0
      for testentry in tests_to_run.iter() {
        let (test_file, expected_failures) : (Value, Value) = if atom(testentry) {
          (testentry, Nil)
        } else {
          (
            second(testentry),
            // Support the expected failures list in two formats:
            //   ((mlist) "test" 1 2 3)
            //   ((mlist) "test" ((mlist) 1 2 3))
            // The first is the old style whereas the second is the new
            // style.
            if consp(caddr(testentry)) {
              cdr(caddr(testentry))
            } else {
              cddr(testentry)
            },
          )
        }
        let test_file_path = d_file_search(
          test_file,
          paths=symval(q_d_file_search_tests),
        )
        suprv1__fmt(t, "Running tests in ~a: ", [
          if symbolp(test_file) {
            Str(princ_to_string(test_file).substring(start=1))
          } else {
            test_file
          },
        ])
        |> ignore
        if debug_.truthy() {
          suprv1__fmt(t, "(~A) ", [test_file_path]) |> ignore
        }
        let ok = mload__errset(() => {
          // Set $BATCH_ANSWERS_FROM_FILE here (again) before each test,
          // because some tests call reset(), which resets it to NIL.
          set(q_d_batch_answers_from_file, answers_from_file) |> ignore
          let (filename, diff, upass, test_count) = test_batch(
            test_file_path,
            expected_failures,
            show_expected=display_known_bugs,
            show_all=display_all,
            showtime=time,
          )
          total_count += to_int(test_count)
          if rest(diff).truthy() || rest(upass).truthy() {
            error_count += length(rest(diff))
            if rest(diff).truthy() {
              errs = cons(cons(filename, rest(diff)), errs)
            }
            if rest(upass).truthy() {
              unexpected_pass = cons(cons(filename, rest(upass)), unexpected_pass)
            }
          }
          t
        })
        if ok is None {
          let error_break_file = format(Nil, "~a", [test_file])
          errs = cons(list([error_break_file, Str("error break")]), errs)
          suprv1__fmt(t, "~%Caused an error break: ~a", [test_file]) |> ignore
          // If the test failed because we couldn't find the file, make a
          // note of that.
          if test_file_path is Nil {
            suprv1__fmt(t, ": test file not found.", []) |> ignore
          }
          suprv1__fmt(t, "~%", []) |> ignore
        }
      }
      print_testsuite_summary(
        errs,
        unexpected_pass,
        int(error_count),
        int(total_count),
      )
      |> ignore
      // CL's TIME report (abridged).
      let real = to_double(num_sub(macsys__real_time(), start_real)) /
        macsys__units_per_second
      let run = to_double(num_sub(macsys__run_time(), start_run)) /
        macsys__units_per_second
      suprv1__fmt(
        {
          let to = symval(sym("*trace-output*"))
          if to is Stream(_) { to } else { t }
        },
        "Evaluation took:~%  ~,3F seconds of real time~%  ~,6F seconds of total run time~%",
        [Flo(real), Flo(run)],
      )
      |> ignore
      q_d_done
    },
  )
  ignore(done)
  disable_some_lisp_warnings() |> ignore
  (q_d_done, Nil)
}

///|
fn init_mload() -> Unit raise {
  defvar_init(q_d_file_type_lisp, list([list1(q_mlist), Str("l"), Str("lsp"), Str("lisp")]))
  defvar_init(
    q_d_file_type_maxima,
    list([
      list1(q_mlist),
      Str("mac"),
      Str("mc"),
      Str("demo"),
      Str("dem"),
      Str("dm1"),
      Str("dm2"),
      Str("dm3"),
      Str("dmt"),
      Str("wxm"),
      Str("wxmx"),
    ]),
  )
  defvar_init(q_d_file_type_wxmx, list([list1(q_mlist), Str("wxmx")]))
  defvar_init(q_d_float_approx_equal_tolerance, Flo(8.0 * double_float_epsilon))
  defvar_init(q_ear_directory_cache, make_hash_table(kind=HashTest::Equal))
  defvar_init(
    q_d_file_search_ignore_dirs,
    list([
      list1(q_mlist),
      Str(".bzr"),
      Str(".git"),
      Str(".github"),
      Str(".hg"),
      Str(".svn"),
      Str(".eclipse"),
      Str(".idea"),
      Str(".vs"),
      Str(".vscode"),
      Str(".zed"),
    ]),
  )
  putprop(
    q_d_file_search_ignore_dirs,
    lfunc("file_search_ignore_dirs-assign", args => {
      let val = arg(args, 1)
      let ok = listp(val) &&
        eq(caar(val), q_mlist) &&
        every(x => stringp(x), cdr(val))
      if !ok {
        mseterr(
          arg(args, 0),
          val,
          reason=Str("Must be a list of strings or an empty list"),
        )
        |> ignore
      }
      Nil
    }),
    q_assign,
  )
  |> ignore
  putprop(
    q_d_file_search_cache,
    lfunc("file_search_cache-assign", args => {
      let val = arg(args, 1)
      if !(val is Nil || eq(val, t) || eq(val, q_d_auto)) {
        mseterr(arg(args, 0), val, reason=Str("must be one of: false, true, auto"))
        |> ignore
      }
      Nil
    }),
    q_assign,
  )
  |> ignore
}
