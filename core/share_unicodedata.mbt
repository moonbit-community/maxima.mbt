// Port of share/contrib/unicodedata/unicodedata.lisp (Leo Butler, 2015):
// rewrite Maxima's ALPHABETP to handle wide characters, and let the user
// alter the table of alphabetic characters at runtime.
//
// The CL file defines its functions inside a LET/LABELS closure over two
// hash tables; the port keeps the tables in file-private globals and
// registers the user-level functions when the file is loaded.

///|
/// Code point -> (char-sym description category) from the data file.
let share_unicodedata__unicode_data : Value = make_hash_table(kind=Eql)

///|
/// Known (reversed) prefixes of alphabetic wide characters.
let share_unicodedata__alphabetp_table : Value = make_hash_table(kind=Equal)

///|
/// The characters seen so far of a possible wide character, most recent
/// first.
let share_unicodedata__stack : Ref[Value] = Ref(Nil)

///|
fn share_unicodedata__description(x : Value) -> Value raise {
  Str(symbol_name(cadr(x)))
}

///|
fn share_unicodedata__category(x : Value) -> Value raise {
  Str(symbol_name(caddr(x)))
}

///|
fn share_unicodedata__lookup(i : Value) -> Value raise {
  Str(symbol_name(car(gethash(i, share_unicodedata__unicode_data))))
}

///|
fn share_unicodedata__create_selector(
  regexp : Value,
) -> ((Value) -> Bool raise) raise {
  match regexp {
    Str(r) => {
      let s = string_downcase(r)
      fn(x : Value) -> Bool raise {
        string_downcase(share_mathml__str(x)).contains(s)
      }
    }
    _ =>
      if eq(regexp, q_d_all) {
        _ => true
      } else if regexp is Nil {
        _ => false
      } else {
        merr("regexp must be a string, the symbol `all' or empty.", [])
        |> ignore
        _ => false
      }
  }
}

///|
fn share_unicodedata__create_adder(
  lookup_char : (Value) -> Value raise,
) -> (Value, Value) -> Value raise {
  fn(regexp : Value, append : Value) -> Value raise {
    let selector = share_unicodedata__create_selector(regexp)
    if append is Nil {
      clrhash(share_unicodedata__alphabetp_table) |> ignore
    }
    maphash(
      (k, v) => if k.truthy() && selector(lookup_char(v)) {
        share_unicodedata__set_alpha_char(k) |> ignore
      },
      share_unicodedata__unicode_data,
    )
    q_d_done
  }
}

///|
fn share_unicodedata__unicode_alphabetp(c : Value) -> Value raise {
  let code = match c {
    Char(ch) => ch.to_int()
    _ => 0
  }
  if code < 128 {
    // this character is ascii and must be non-alphabetic; there are no
    // characters on the stack nor known to be part of a wide-character
    share_unicodedata__stack.val = Nil
    Nil
  } else if share_unicodedata__stack.val is Nil {
    // len=0
    share_unicodedata__stack.val = cons(c, share_unicodedata__stack.val)
    if gethash(share_unicodedata__stack.val, share_unicodedata__alphabetp_table).truthy() {
      share_unicodedata__stack.val
    } else {
      share_unicodedata__stack.val = Nil
      Nil
    }
  } else {
    // 1 or more characters in stack
    share_unicodedata__stack.val = cons(c, share_unicodedata__stack.val)
    if gethash(share_unicodedata__stack.val, share_unicodedata__alphabetp_table).truthy() {
      // c is part of wide-character
      share_unicodedata__stack.val
    } else {
      // c is not end of wide-character, but it may start new one.
      share_unicodedata__stack.val = Nil
      share_unicodedata__unicode_alphabetp(c)
    }
  }
}

///|
/// The redefined ALPHABETP (src/nparse.lisp), using UNICODE-ALPHABETP.
fn share_unicodedata__alphabetp(n : Value) -> Value raise {
  match n {
    Char(c) =>
      if alpha_char_p(c) || member(n, symval(q_ear_alphabet)).truthy() {
        share_unicodedata__stack.val = Nil
        t
      } else {
        share_unicodedata__unicode_alphabetp(n)
      }
    _ => Nil
  }
}

///|
/// set_alpha_char(char): add a wide character to the hashtable of known
/// alphabetical characters.
fn share_unicodedata__set_alpha_char(char_sym : Value) -> Value raise {
  let s = match char_sym {
    Str(s) => s
    Sym(_) => symbol_name(char_sym)
    Fix(n) if n > 127L && n < 917999L =>
      match n.to_int().to_char() {
        Some(c) => c.to_string()
        None => ""
      }
    _ => {
      merr("first argument must be a string, symbol or integer", []) |> ignore
      ""
    }
  }
  let char_sym_list = list(string_chars(s).map(c => Value::Char(c)))
  let mut x = reverse(char_sym_list)
  while x.truthy() {
    sethash(x, share_unicodedata__alphabetp_table, t) |> ignore
    x = cdr(x)
  }
  q_d_done
}

///|
/// unicode_init([regexp [, file]]): read the Unicode data file and, if
/// REGEXP is given, add the matching characters.
fn share_unicodedata__unicode_init(regexp : Value, file : Value) -> Value raise {
  let data_file = mfuncall(
    q_d_file_search1,
    list([
      if file.truthy() {
        file
      } else {
        Str("unicodedata-txt.lisp")
      },
      list([list1(q_mlist), q_d_file_search_lisp]),
    ]),
  )
  let entries = share_unicodedata__read_data_file(share_mathml__str(data_file))
  for e in entries.iter() {
    let n = car(e)
    sethash(
      n,
      share_unicodedata__unicode_data,
      list([cadr(e), caddr(e), cadddr(e)]),
    )
    |> ignore
  }
  if regexp.truthy() {
    share_unicodedata__unicode_add(regexp, Nil)
  } else {
    Nil
  }
}

///|
fn share_unicodedata__unicode_add_category(
  category : Value,
  append : Value,
) -> Value raise {
  (share_unicodedata__create_adder(share_unicodedata__category))(
    category, append,
  )
}

///|
/// unicode_add([regexp [, append]]): select the wide characters whose
/// description contains REGEXP; if REGEXP is the symbol `all', all of them;
/// if REGEXP is false, none (the table is emptied unless APPEND).
fn share_unicodedata__unicode_add(regexp : Value, append : Value) -> Value raise {
  if listp(regexp) && regexp.truthy() {
    let r = Collector::new()
    let mut app = append
    for regex in cdr(regexp).iter() {
      r.add(share_unicodedata__unicode_add(regex, app))
      app = t
    }
    cons(list1(q_mlist), r.result())
  } else {
    let n = hash_table_count(share_unicodedata__alphabetp_table)
    (share_unicodedata__create_adder(share_unicodedata__description))(
      regexp, append,
    )
    |> ignore
    list([
      list1(q_mlist),
      regexp,
      int(hash_table_count(share_unicodedata__alphabetp_table) - n),
    ])
  }
}

///|
fn share_unicodedata__print_hashtable(ht : Value) -> Value raise {
  with_specials(
    [(sym("*print-base*"), Fix(16L)), (sym("*print-radix*"), t)],
    () => {
      maphash(
        (k, v) => format(t, "(~a  ~{~s ~})~%", [
          k,
          if listp(v) {
            v
          } else {
            list1(v)
          },
        ])
        |> ignore,
        ht,
      )
      Nil
    },
  )
}

// Reading the data file. unicodedata-txt.lisp holds one form,
// #.(list '(#x1EEF1 |c| |DESCRIPTION| |Sm| ...) ...), read with READ;
// the port's Lisp reader has no #x or #. syntax, so the form is read here.

///|
struct ShareUnicodedataReader {
  cs : Array[Char]
  mut i : Int
}

///|
fn ShareUnicodedataReader::skip_ws(self : ShareUnicodedataReader) -> Unit {
  while self.i < self.cs.length() {
    let c = self.cs[self.i]
    if c == ';' {
      while self.i < self.cs.length() && self.cs[self.i] != '\n' {
        self.i += 1
      }
    } else if c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c' {
      self.i += 1
    } else {
      break
    }
  }
}

///|
fn ShareUnicodedataReader::token_text(self : ShareUnicodedataReader) -> String {
  let sb = StringBuilder::new()
  while self.i < self.cs.length() {
    let c = self.cs[self.i]
    if " \t\n\r()'\";".contains_char(c) {
      break
    }
    if c == '|' {
      sb.write_char(c)
      self.i += 1
      while self.i < self.cs.length() && self.cs[self.i] != '|' {
        if self.cs[self.i] == '\\' {
          sb.write_char(self.cs[self.i])
          self.i += 1
        }
        sb.write_char(self.cs[self.i])
        self.i += 1
      }
      sb.write_char('|')
      self.i += 1
    } else {
      sb.write_char(c)
      self.i += 1
    }
  }
  sb.to_string()
}

///|
fn ShareUnicodedataReader::read(self : ShareUnicodedataReader) -> Value raise {
  self.skip_ws()
  if self.i >= self.cs.length() {
    raise LispError::SimpleError("end of file on the Unicode data stream")
  }
  let c = self.cs[self.i]
  match c {
    '(' => {
      self.i += 1
      let items = Collector::new()
      while true {
        self.skip_ws()
        if self.i >= self.cs.length() {
          raise LispError::SimpleError("end of file on the Unicode data stream")
        }
        if self.cs[self.i] == ')' {
          self.i += 1
          break
        }
        items.add(self.read())
      }
      items.result()
    }
    '\'' => {
      self.i += 1
      list([q_quote, self.read()])
    }
    '#' => {
      self.i += 1
      let d = self.cs[self.i]
      self.i += 1
      match d {
        'x' | 'X' => {
          let tok = self.token_text()
          match share_unicodedata__parse_hex(tok) {
            Some(n) => n
            None =>
              raise LispError::SimpleError("bad hexadecimal number #x" + tok)
          }
        }
        '.' => share_unicodedata__eval(self.read())
        _ =>
          raise LispError::SimpleError(
            "unsupported dispatch #" + d.to_string() + " in the Unicode data",
          )
      }
    }
    _ => lread(self.token_text())
  }
}

///|
fn share_unicodedata__parse_hex(tok : String) -> Value? {
  if tok.length() == 0 {
    return None
  }
  let mut n = 0L
  for c in string_chars(tok) {
    let d = if c >= '0' && c <= '9' {
      c.to_int() - '0'.to_int()
    } else if c >= 'a' && c <= 'f' {
      c.to_int() - 'a'.to_int() + 10
    } else if c >= 'A' && c <= 'F' {
      c.to_int() - 'A'.to_int() + 10
    } else {
      return None
    }
    n = n * 16L + d.to_int64()
  }
  Some(Fix(n))
}

///|
/// Read-time evaluation (#.) of the forms the data file uses: (LIST ...)
/// of quoted data and self-evaluating atoms.
fn share_unicodedata__eval(form : Value) -> Value raise {
  match form {
    Cons(_) =>
      if eq(car(form), q_list) {
        mapcar(e => share_unicodedata__eval(e), cdr(form))
      } else if eq(car(form), q_quote) {
        cadr(form)
      } else {
        raise LispError::SimpleError(
          "unsupported read-time form in the Unicode data: " +
          prin1_to_string(form),
        )
      }
    Sym(_) =>
      raise LispError::SimpleError(
        "unsupported read-time form in the Unicode data: " +
        prin1_to_string(form),
      )
    _ => form
  }
}

///|
fn share_unicodedata__read_data_file(path : String) -> Value raise {
  let r : ShareUnicodedataReader = {
    cs: string_chars(read_file(path)),
    i: 0,
  }
  r.read()
}

///|
fn init_share_unicodedata() -> Unit raise {
  // redefine alphabetp from src/nparse.lisp to use unicode-alphabetp
  nparse__alphabetp_redefined.val = Some(share_unicodedata__alphabetp)
  defun(
    sym("unicode-alphabetp"),
    a => share_unicodedata__unicode_alphabetp(arg(a, 0)),
    name="unicode-alphabetp",
  )
  defun(
    q_alphabetp,
    a => share_unicodedata__alphabetp(arg(a, 0)),
    name="alphabetp",
  )
  defun(
    sym("$set_alpha_char"),
    a => {
      check_arity("set_alpha_char", a, 1)
      share_unicodedata__set_alpha_char(arg(a, 0))
    },
    name="$set_alpha_char",
  )
  defun(
    sym("$unicode_init"),
    a => {
      check_arity_range("unicode_init", a, 0, 2)
      share_unicodedata__unicode_init(arg(a, 0), arg(a, 1))
    },
    name="$unicode_init",
  )
  defun(
    sym("$unicode_add_category"),
    a => {
      check_arity_range("unicode_add_category", a, 1, 2)
      share_unicodedata__unicode_add_category(arg(a, 0), arg(a, 1))
    },
    name="$unicode_add_category",
  )
  defun(
    sym("$unicode_add"),
    a => {
      check_arity_range("unicode_add", a, 0, 2)
      share_unicodedata__unicode_add(arg(a, 0), arg(a, 1))
    },
    name="$unicode_add",
  )
  defun(
    sym("print-hashtable"),
    a => share_unicodedata__print_hashtable(
      if a.length() > 0 {
        a[0]
      } else {
        share_unicodedata__unicode_data
      },
    ),
    name="print-hashtable",
  )
  defun(
    sym("print-alphabetp-hashtable"),
    _ => share_unicodedata__print_hashtable(
      share_unicodedata__alphabetp_table,
    ),
    name="print-alphabetp-hashtable",
  )
}

///|
/// share/contrib/unicodedata/unicodedata-txt.lisp is the data file read by
/// unicode_init; loading it evaluates its one form, a list of the data,
/// with no other effect.
fn init_share_unicodedata_txt() -> Unit raise {
  ()
}
