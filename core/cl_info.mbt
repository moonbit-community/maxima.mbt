// Port of src/cl-info.lisp: the help system's topic lookup ("? foo",
// "?? foo", describe) over the index built ahead of time from the info
// manual (maxima-index.lisp, maxima-index-html.lisp in the info directory,
// loaded by LOAD-PRIMARY-INDEX).
//
// *INFO-TABLES* maps an info directory to a list of two EQUAL hash tables
// (section table, deffn/defvr table) from a topic name to
// (filename byte-offset char-count node-name heading-title).

///|
let cl_info__q_noop : Value = sym("noop")

///|
let cl_info__q_all : Value = sym("all")

///|
let cl_info__q_none : Value = sym("none")

///|
fn info_print_prompt(prompt_count : Value) -> Value raise {
  fresh_line(stream=symval(standard_output)) |> ignore
  format_prompt(
    t,
    Str("~a"),
    list1(
      Str(
        if zerop(prompt_count) {
          "Enter space-separated numbers, `all' or `none': "
        } else {
          "Still waiting: "
        },
      ),
    ),
  )
}

///|
/// (parse-integer line :start pos :junk-allowed t): the integer (or NIL)
/// and the index where parsing stopped.
fn cl_info__parse_integer_junk(cs : Array[Char], start : Int) -> (Value, Int) {
  let n = cs.length()
  let mut i = start
  while i < n && (cs[i] == ' ' || cs[i] == '\t' || cs[i] == '\n' || cs[i] == '\r') {
    i += 1
  }
  if i >= n {
    return (Nil, n)
  }
  let mut minusp = false
  if cs[i] == '-' {
    minusp = true
    i += 1
  } else if cs[i] == '+' {
    i += 1
  }
  let digits = StringBuilder::new()
  while i < n && digit_char_p(cs[i]) is Some(_) {
    digits.write_char(cs[i])
    i += 1
  }
  let d = digits.to_string()
  if d == "" {
    (Nil, i)
  } else {
    match parse_integer((if minusp { "-" } else { "" }) + d) {
      Some(v) => (v, i)
      None => (Nil, i)
    }
  }
}

///|
fn info_parse_user_choice(nitems : Value) -> Value raise {
  let line = match read_line(stream=symval(standard_input)) {
    Some(l) => l
    None =>
      raise LispError::SimpleError(
        "end of file on " + prin1_to_string(symval(standard_input)),
      )
  }
  let cs = string_chars(line)
  let list = Collector::new()
  let mut pos = 0
  while true {
    let (nth_, p) = cl_info__parse_integer_junk(cs, pos)
    pos = p
    if nth_ is Nil {
      break
    }
    if minusp(nth_) || num_ge(nth_, nitems) {
      suprv1__fmt(symval(q_ear_debug_io), "~&Discarding invalid number ~d.", [nth_])
      |> ignore
    } else {
      list.add(nth_)
    }
  }
  let rest = string_right_trim(" \t\n;", chars_to_string(cs[pos:].to_array()))
  let mut keyword : Value = Nil
  for entry in symval(q_n_plusselect_by_keyword_alist_plus).iter() {
    let mut found = false
    for s in cdr(entry).iter() {
      if string_equal(rest, lstring(s)) {
        found = true
        break
      }
    }
    if found {
      keyword = car(entry)
      break
    }
  }
  if keyword is Nil {
    keyword = cl_info__q_noop
    suprv1__fmt(symval(q_ear_debug_io), "~&Ignoring trailing garbage in input.", [])
    |> ignore
  }
  cons(keyword, list.result())
}

///|
fn info_select_info_items(selection : Value, items : Value) -> Value raise {
  let key = car(selection)
  let selection = cdr(selection)
  if eq(key, cl_info__q_noop) {
    mapcar(i => nth(to_int(i), items), selection)
  } else if eq(key, cl_info__q_all) {
    items
  } else if eq(key, cl_info__q_none) {
    cl_info__q_none
  } else {
    Nil
  }
}

// ------------------ search help topics ------------------

///|
/// Splice a "/" between the path components given as arguments, collapsing
/// multiple consecutive slashes into a single slash.
fn info_combine_path(list_ : Value) -> Value raise {
  let raw_path = lstring(format(Nil, "~{~A~^/~}", [list_]))
  let out = StringBuilder::new()
  let mut prev_slash = false
  for c in raw_path {
    if c == '/' {
      if !prev_slash {
        out.write_char(c)
        prev_slash = true
      }
    } else {
      out.write_char(c)
      prev_slash = false
    }
  }
  Str(out.to_string())
}

///|
/// WARN, as SBCL prints it on *ERROR-OUTPUT*.
fn cl_info__warn(msg : String) -> Unit {
  flush_stdout()
  write_stderr("WARNING: " + msg + "\n")
}

///|
/// The text of the warning LOAD-PRIMARY-INDEX gives when it cannot load
/// PATH, laid out as SBCL's pretty printer does.
fn cl_info__index_warning(detail_lines : Array[String]) -> String {
  let prefix = "(Details: CL-INFO::LOAD-PRIMARY-INDEX: "
  let indent = " ".repeat(string_length(prefix))
  let sb = StringBuilder::new()
  sb.write_string("Maxima is unable to set up the help system.\n")
  sb.write_string(prefix)
  for i, l in detail_lines {
    if i > 0 {
      sb.write_string("\n" + indent)
    }
    sb.write_string(l)
  }
  sb.write_string(")\n")
  sb.to_string()
}

///|
/// (load path) of an index file, with the HANDLER-CASE of
/// LOAD-PRIMARY-INDEX around it.
fn cl_info__load_index(path : String) -> Unit {
  if !probe_file(path) {
    cl_info__warn(
      cl_info__index_warning([
        "Couldn't load", "\"" + path + "\":", "file does not exist.",
      ]),
    )
    return
  }
  // (with-standard-io-syntax (load path-to-index))
  (fn() raise { lisp_load_file(path) })() catch {
    e => cl_info__warn(cl_info__index_warning([suprv1__error_text(e)]))
  }
}

///|
fn info_load_primary_index() -> Value raise {
  let lang = symval(q_ear_maxima_lang_subdir)
  let subdir_bit = if lang.truthy() { lang } else { Str(".") }
  let infodir = symval(q_ear_maxima_infodir)
  let path_to_index = info_combine_path(
    list([infodir, subdir_bit, Str("maxima-index.lisp")]),
  )
  let path_to_html_index = info_combine_path(
    list([infodir, subdir_bit, Str("maxima-index-html.lisp")]),
  )
  // Set the default of the html URL base to be a file URL pointing to the
  // info dir.
  let htmldir = symval(q_ear_maxima_htmldir)
  set(
    q_d_url_base,
    Str(
      "file://" +
      lstring(
        if lang.truthy() {
          info_combine_path(list([htmldir, lang]))
        } else {
          htmldir
        },
      ),
    ),
  )
  |> ignore
  // Make reset() restore this value rather than the DEFMVAR default.
  let tbl = symval(q_ear_variable_initial_values)
  if hash_table_p(tbl) {
    sethash(q_d_url_base, tbl, symval(q_d_url_base)) |> ignore
  }
  cl_info__load_index(lstring(path_to_index))
  cl_info__load_index(lstring(path_to_html_index))
  Nil
}

///|
fn info_info_exact(x : Value) -> Value raise {
  let x = info_strip_quotes(x)
  let exact_matches = info_exact_topic_match(x)
  if !info_some_exact(x, exact_matches).truthy() {
    format(
      t,
      "  No exact match found for topic `~a'.~%  Try `?? ~a' (inexact match) instead.~%~%",
      [x, x],
    )
    |> ignore
    Nil
  } else {
    info_display_items(exact_matches) |> ignore
    if info_some_inexact(x, info_inexact_topic_match(x)).truthy() {
      format(
        t,
        "  There are also some inexact matches for `~a'.~%  Try `?? ~a' to see them.~%~%",
        [x, x],
      )
      |> ignore
    }
    t
  }
}

///|
fn info_some_exact(x : Value, matches : Value) -> Value raise {
  for v in info_flatten_matches(x, matches).iter() {
    if v.truthy() {
      return v
    }
  }
  Nil
}

///|
fn info_some_inexact(x : Value, matches : Value) -> Value raise {
  for v in info_flatten_matches(x, matches).iter() {
    if v is Nil {
      return t
    }
  }
  Nil
}

///|
fn info_flatten_matches(x : Value, matches : Value) -> Value raise {
  // OH GODS, SPARE YOUR SERVANT FROM YOUR FIERY WRATH ...
  let all = append_n(list_to_array(mapcar(m => second(m), matches)))
  mapcar(y => lbool(equal(y, x)), mapcar(m => first(m), all))
}

///|
fn info_exact_topic_match(topic : Value) -> Value raise {
  let topic = info_regex_sanitize(topic)
  let r = Collector::new()
  for dir_name in cl_info__hash_keys(symval(q_ear_info_tables)) {
    r.add(list2(dir_name, info_exact_topic_match_1(topic, dir_name)))
  }
  r.result()
}

///|
/// The keys of a hash table, in iteration order.
fn cl_info__hash_keys(table : Value) -> Array[Value] raise {
  let keys : Array[Value] = []
  maphash((k, _v) => keys.push(k), table)
  keys
}

///|
fn info_exact_topic_match_1(topic : Value, d : Value) -> Value raise {
  let tables = gethash(d, symval(q_ear_info_tables))
  let section_table = first(tables)
  let defn_table = second(tables)
  let regex1 : Value = Str("^" + lstring(topic) + "$")
  let regex2 : Value = Str("^" + lstring(topic) + " *<[0-9]+>$")
  append_n([
    info_find_regex_matches(regex1, section_table),
    info_find_regex_matches(regex1, defn_table),
    info_find_regex_matches(regex2, section_table),
    info_find_regex_matches(regex2, defn_table),
  ])
}

///|
fn info_info_inexact(x : Value) -> Value raise {
  let x = info_strip_quotes(x)
  let inexact_matches = info_inexact_topic_match(x)
  if inexact_matches.truthy() {
    info_display_items(inexact_matches) |> ignore
  }
  lbool(inexact_matches.truthy())
}

///|
/// MATCHES looks like ((D1 (I11 I12 I12 ...)) (D2 (I21 I22 I23 ...)))
/// Rearrange it to ((D1 I11) (D1 I12) (D1 I13) ... (D2 I21) (D2 I22) ...)
fn info_rearrange_matches(matches : Value) -> Value raise {
  let r = Collector::new()
  for di in matches.iter() {
    let d = first(di)
    let i = second(di)
    for i1 in i.iter() {
      r.add(list2(d, i1))
    }
  }
  r.result()
}

///|
fn info_display_items(items : Value) -> Value raise {
  let items_list = info_rearrange_matches(items)
  let nitems = length(items_list)
  let mut i = 0
  for item in items_list.iter() {
    if nitems > 1 {
      let heading_title = nth(4, second(item))
      let item_name = first(second(item))
      format(t, "~% ~d: ~a~@[  (~a)~]", [int(i), item_name, heading_title])
      |> ignore
    }
    i += 1
  }
  let wanted = if nitems > 1 {
    let mut prompt_count = 0
    let mut w : Value = Nil
    while true {
      finish_output(stream=symval(q_ear_debug_io))
      info_print_prompt(int(prompt_count)) |> ignore
      finish_output(stream=symval(standard_output))
      w = info_select_info_items(
        info_parse_user_choice(int(nitems)),
        items_list,
      )
      if w.truthy() {
        break
      }
      prompt_count += 1
    }
    w
  } else {
    items_list
  }
  finish_output(stream=symval(q_ear_debug_io))
  if consp(wanted) {
    format(t, "~%", []) |> ignore
    funcall(symval(q_ear_help_display_function), [wanted])
  } else {
    Nil
  }
}

///|
fn info_inexact_topic_match(topic : Value) -> Value raise {
  let topic = info_regex_sanitize(topic)
  let foo = Collector::new()
  for dir_name in cl_info__hash_keys(symval(q_ear_info_tables)) {
    foo.add(list2(dir_name, info_inexact_topic_match_1(topic, dir_name)))
  }
  remove_if(x => second(x) is Nil, foo.result())
}

///|
fn info_inexact_topic_match_1(topic : Value, d : Value) -> Value raise {
  let tables = gethash(d, symval(q_ear_info_tables))
  let section_table = first(tables)
  let defn_table = second(tables)
  append(
    info_find_regex_matches(topic, section_table),
    info_find_regex_matches(topic, defn_table),
  )
}

///|
/// If S is enclosed in single quotes or double quotes, return the quoted
/// string.
fn info_strip_quotes(s : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  let n = cs.length()
  if n <= 2 {
    // incidentally return "" or '' verbatim
    s
  } else {
    let first_char = cs[0]
    let last_char = cs[n - 1]
    if (first_char == '\'' && last_char == '\'') ||
      (first_char == '"' && last_char == '"') {
      Str(chars_to_string(cs[1:n - 1].to_array()))
    } else {
      s
    }
  }
}

///|
/// Precede any regex special characters with a backslash.
fn info_regex_sanitize(s : Value) -> Value raise {
  rx_pregexp_quote(s)
}

///|
/// STRING-LESSP: compare ignoring case (case folded to lower case).
fn cl_info__string_lessp(a : String, b : String) -> Bool {
  let x = string_chars(a)
  let y = string_chars(b)
  let n = if x.length() < y.length() { x.length() } else { y.length() }
  for i in 0..<n {
    let c = char_downcase(x[i]).to_int()
    let d = char_downcase(y[i]).to_int()
    if c != d {
      return c < d
    }
  }
  x.length() < y.length()
}

///|
fn info_find_regex_matches(regex_string : Value, hashtable : Value) -> Value raise {
  // Do the search ignoring case by wrapping the regex-string in "(?i:...)"
  let regex : Value = Str("(?i:" + lstring(regex_string) + ")")
  let mut regex_matches : Value = Nil
  let compiled = rx_pregexp(regex)
  maphash(
    (key, value) => if rx_pregexp_match_positions(compiled, key).truthy() {
      regex_matches = cons(cons(key, value), regex_matches)
    },
    hashtable,
  )
  // (stable-sort regex-matches #'string-lessp :key #'car)
  let arr = list_to_array(regex_matches)
  let sorted = arr.copy()
  // insertion sort keeps equal keys in order (stable)
  for i in 1..<sorted.length() {
    let x = sorted[i]
    let mut j = i - 1
    while j >= 0 &&
          cl_info__string_lessp(lstring(car(x)), lstring(car(sorted[j]))) {
      sorted[j + 1] = sorted[j]
      j -= 1
    }
    sorted[j + 1] = x
  }
  list(sorted)
}

///|
/// The directory pathname DIR-NAME merged with the file name FILENAME.
fn cl_info__merge_path(filename : String, dir_name : Value) -> String {
  let dir = princ_to_string(dir_name)
  if dir == "" || dir.has_suffix("/") {
    dir + filename
  } else {
    // (merge-pathnames name dir): the directory part of DIR.
    match dir.rev_find("/") {
      Some(k) => dir.substring(end=k + 1) + filename
      None => filename
    }
  }
}

///|
/// Decode UTF-8 OCTETS[start:] into at most COUNT characters.
fn cl_info__decode_utf8(octets : Bytes, start : Int, count : Int) -> String {
  let sb = StringBuilder::new()
  let n = octets.length()
  let mut i = start
  let mut k = 0
  while i < n && k < count {
    let b = octets[i].to_int()
    let (len, init) = if b < 0x80 {
      (1, b)
    } else if b < 0xe0 {
      (2, b & 0x1f)
    } else if b < 0xf0 {
      (3, b & 0x0f)
    } else {
      (4, b & 0x07)
    }
    let mut code = init
    for j in 1..<len {
      if i + j < n {
        code = (code << 6) | (octets[i + j].to_int() & 0x3f)
      }
    }
    sb.write_char(code.unsafe_to_char())
    i += len
    k += 1
  }
  sb.to_string()
}

///|
fn info_read_info_text(dir_name : Value, parameters : Value) -> Value raise {
  let value = cdr(parameters)
  let filename = car(value)
  let byte_offset = cadr(value)
  let char_count = caddr(value)
  let path_filename = cl_info__merge_path(lstring(filename), dir_name)
  let octets = (fn() -> Bytes raise { read_file_bytes(path_filename) })() catch {
    _ =>
      return merr(
        "Cannot find documentation for `~M': missing info file ~M~%",
        [car(parameters), Str(path_filename)],
      )
  }
  if !plusp(byte_offset) {
    // If byte-offset isn't positive there must be some error in the index.
    // Return nil and let the caller deal with it.
    return Nil
  }
  // (read-sequence text in :start 0 :end char-count) on a string made by
  // (make-string char-count): characters not read stay as they were.
  let text = cl_info__decode_utf8(octets, to_int(byte_offset), to_int(char_count))
  let missing = to_int(char_count) - string_length(text)
  Str(
    if missing > 0 {
      text + String::make(missing, '\u{0}')
    } else {
      text
    },
  )
}

// --------------- build help topic indices ---------------

///|
fn info_load_info_hashtables(
  dir_name : Value,
  deffn_defvr_pairs : Value,
  section_pairs : Value,
) -> Value raise {
  if length(section_pairs) == 0 && length(deffn_defvr_pairs) == 0 {
    format(t, "warning: ignoring an empty documentation index in ~a~%", [
      dir_name,
    ])
  } else {
    let tables = info_ensure_info_tables(dir_name)
    let section_hashtable = first(tables)
    let deffn_defvr_hashtable = second(tables)
    for x in section_pairs.iter() {
      sethash(car(x), section_hashtable, cdr(x)) |> ignore
    }
    for x in deffn_defvr_pairs.iter() {
      sethash(car(x), deffn_defvr_hashtable, cdr(x)) |> ignore
    }
    deffn_defvr_pairs
  }
}

///|
fn info_ensure_info_tables(dir_name : Value) -> Value raise {
  let existing = gethash(dir_name, symval(q_ear_info_tables))
  if existing.truthy() {
    existing
  } else {
    let t1 = make_hash_table(kind=HashTest::Equal)
    let t2 = make_hash_table(kind=HashTest::Equal)
    sethash(dir_name, symval(q_ear_info_tables), list2(t1, t2))
  }
}

///|
fn info_load_html_index(entries : Value) -> Value raise {
  let index = symval(q_ear_html_index)
  clrhash(index) |> ignore
  // Go through the entries and add it to the html index hashtable.  Each
  // entry is a list of 3 items: the item key for the hash table, the path
  // to the html file containing the item we're interested in and the html
  // id for the item.
  for entry in entries.iter() {
    let item = nth(0, entry)
    let path = nth(1, entry)
    let id = nth(2, entry)
    sethash(item, index, cons(path, id)) |> ignore
  }
  Nil
}

///|
fn init_cl_info() -> Unit raise {
  defvar_init(q_ear_info_tables, make_hash_table(kind=HashTest::Equal))
  // Hash table for looking up which html file contains the documentation.
  // The key is the topic we're looking for and the value is a cons
  // consisting of the html file and the id for the key.
  defvar_init(q_ear_html_index, make_hash_table(kind=HashTest::Equal))
}
