// Port of share/contrib/maximaMathML/PrMathML.lisp: generate Presentation
// MathML code from Maxima (Paul S. Wang, Kent State University, 1999).

///|
/// The special *INDENT* (declaimed special, never DEFVARed).
let share_prmathml__q_indent : Value = sym("*indent*")

///|
/// The special MPRPORT: the output stream of the MathML printers.
let share_prmathml__q_mprport : Value = sym("mprport")

///|
fn share_prmathml__port() -> Value raise {
  symval(share_prmathml__q_mprport)
}

///|
fn share_prmathml__ccol() -> Int raise {
  to_int(symval(q_ccol))
}

///|
/// prmathml(expr, [,(filename|stream)[,t (d)]]): generate MathML
/// presentation codes for the expression.
fn d_prmathml(margs : Value) -> Value raise {
  let mut filename : Value = Nil
  let mut file_path = ""
  with_specials(
    [
      (q_ccol, Fix(1L)),
      (q_ear_row, t),
      (share_prmathml__q_indent, Fix(0L)),
      (share_prmathml__q_mprport, Nil),
    ],
    () => {
      let mut mexpress = car(margs)
      let mut mexplabel : Value = Nil
      if mexpress is Nil {
        princ(Str(" NO EXPRESSION GIVEN ")) |> ignore
        return Nil
      } else if cdr(margs) is Nil {
        filename = Nil
        set(share_prmathml__q_mprport, t) |> ignore
      } else if cddr(margs) is Nil {
        let port = if stringp(cadr(margs)) {
          filename = cadr(margs)
          file_path = share_mathml__str(cadr(margs))
          make_string_output_stream()
        } else {
          // otherwise, assume (cadr margs) is a stream.
          cadr(margs)
        }
        set(share_prmathml__q_mprport, port) |> ignore
      } else {
        princ(Str(" wrong No. of Arguments given ")) |> ignore
      }
      if memq(mexpress, symval(q_d_labels)).truthy() {
        mexplabel = sym(
          "(" + princ_to_string(fullstrip1(mexpress)) + ")",
        )
        mexpress = symval(mexpress)
      } else {
        mexplabel = Nil
        if symval(q_d_mprevaluate).truthy() {
          mexpress = meval(mexpress)
        }
      }
      if symval(q_d_mprautolabel).truthy() {
        raise LispError::SimpleError(
          "The function UPDATEAUTOLABEL is undefined.",
        )
      }
      if symbolp(mexpress) {
        let x = d_verbify(mexpress)
        let y = mget(x, q_mexprer)
        if y.truthy() {
          mexpress = list([list1(q_mdefine), cons(list1(x), cdadr(y)), caddr(y)])
        } else {
          let y = mget(x, q_mmacro)
          if y.truthy() {
            mexpress = list([
              list1(q_mdefmacro),
              cons(list1(x), cdadr(y)),
              caddr(y),
            ])
          } else {
            let y = mget(x, q_aexpr)
            if y.truthy() {
              mexpress = list([
                list1(q_mdefine),
                cons(list([x, q_array]), cdadr(y)),
                caddr(y),
              ])
            }
          }
        }
      }
      if consp(mexpress) && consp(car(mexpress)) && eq(q_mlabel, caar(mexpress)) {
        mexpress = cadr(mexpress)
      }
      let port = share_prmathml__port()
      // CL's 'C is the symbol named "C"; EXPLODE of the label makes one
      // symbol per character.
      let label_has_c = () => mexplabel.truthy() &&
        memq(sym("C"), explode(mexplabel)).truthy()
      if symval(q_d_lamprworksheet).truthy() && label_has_c() {
        format(port, "\\begin{verbatim}~%~a ", [mexplabel]) |> ignore
        mgrind(mexpress, port) |> ignore
        format(port, ";~%\\end{verbatim}~%", []) |> ignore
      } else if symval(q_d_mprworksheet).truthy() && label_has_c() {
        format(port, "|~a ", [mexplabel]) |> ignore
        mgrind(mexpress, port) |> ignore
        format(port, ";|~%", []) |> ignore
      } else {
        if symval(q_d_lamprautolabel).truthy() {
          format(port, "\\begin{equation}~%", []) |> ignore
        } else {
          tprinc(Str("<math  xmlns='http://www.w3.org/1998/Math/MathML'>"))
          |> ignore
        }
        mpr_engine(mexpress, q_mparen, q_mparen) |> ignore
        if symval(q_d_lamprautolabel).truthy() {
          format(share_prmathml__port(), "~%\\end{equation}~%", []) |> ignore
        } else if symval(q_d_mprdisplaytype).truthy() {
          if mexplabel.truthy() {
            if symval(q_d_mprlabelleft).truthy() {
              format(share_prmathml__port(), "\\leqno{\\tt ~a}", [mexplabel])
              |> ignore
            } else {
              format(share_prmathml__port(), "\\eqno{\\tt ~a}", [mexplabel])
              |> ignore
            }
          }
          tprinc(Str("</math>")) |> ignore
          myterpri() |> ignore
        } else {
          tprinc(Str("</math>")) |> ignore
        }
      }
      if filename.truthy() {
        let port = share_prmathml__port()
        terpri(stream=port) |> ignore
        mactex__append_to_file(file_path, get_output_stream_string(port))
      }
      q_done
    },
  )
}

///|
/// mPr_engine is the kernel function of this program. It checks whether
/// the argument "mexpress" is an atom or an expression, and then assigns a
/// proper function to the expression, or just prints it if it is an atom.
/// lop, rop - left and right hand side operators of mexpress.
fn mpr_engine(mexpress : Value, lop : Value, rop : Value) -> Value raise {
  with_specials([(q_lop, lop), (q_rop, rop)], () => {
    let mexpress = nformat(mexpress)
    if atom(mexpress) {
      mpr_atom(mexpress)
    } else if listp(car(mexpress)) {
      if memq(q_array, car(mexpress)).truthy() {
        mpr_array(mexpress)
      } else if num_le(mpr_lbp(caar(mexpress)), mpr_rbp(lop)) ||
        num_gt(mpr_lbp(rop), mpr_rbp(caar(mexpress))) {
        mpr_paren(mexpress)
      } else {
        let p = get(caar(mexpress), q_mprprocess)
        if p.truthy() {
          funcall(p, [mexpress])
        } else {
          mpr_function(mexpress)
        }
      }
    } else {
      Nil
    }
  })
}

// Utilities

///|
fn row_begin(str : Value) -> Value raise {
  myterpri() |> ignore
  princ(str, stream=share_prmathml__port()) |> ignore
  set(share_prmathml__q_indent, num_add(symval(share_prmathml__q_indent), Fix(1L)))
  |> ignore
  set(q_ear_row, t)
}

///|
fn myindent() -> Value raise {
  let mut i = symval(share_prmathml__q_indent)
  while !equal(i, Fix(0L)) {
    princ(Str("   "), stream=share_prmathml__port()) |> ignore
    i = num_sub(i, Fix(1L))
  }
  Nil
}

///|
fn row_end(str : Value) -> Value raise {
  set(share_prmathml__q_indent, num_sub(symval(share_prmathml__q_indent), Fix(1L)))
  |> ignore
  myterpri() |> ignore
  princ(str, stream=share_prmathml__port()) |> ignore
  set(q_ear_row, t)
}

///|
fn tpchar(c : Value) -> Value raise {
  set(q_ccol, num_add(symval(q_ccol), Fix(1L))) |> ignore
  princ(c, stream=share_prmathml__port())
}

///|
/// tprinc is an intelligent low level printing routine. It keeps track of
/// the size of the output for purposes of allowing the file to have a
/// reasonable line-length.
fn tprinc(chstr : Value) -> Value raise {
  let chlst = exploden(chstr)
  let linebreak = length(chlst) + share_prmathml__ccol() > 80
  if symval(q_ear_row).truthy() {
    // *row* calls for new row
    set(q_ear_row, Nil) |> ignore
    myterpri() |> ignore
  }
  let mut colc = share_prmathml__ccol()
  for ch in chlst.iter() {
    match ch {
      Char(c) => write_char(c, stream=share_prmathml__port())
      _ => princ(ch, stream=share_prmathml__port()) |> ignore
    }
    // line break only after > (the characters are compared with the
    // symbol >, which never matches)
    if linebreak && eq(ch, sym(">")) {
      myterpri() |> ignore
    }
    colc += 1
  }
  set(q_ccol, int(colc)) |> ignore
  Nil
}

///|
/// myterpri is terpri with port and indent control
fn myterpri() -> Value raise {
  let port = share_prmathml__port()
  if port.truthy() {
    terpri(stream=port) |> ignore
  } else {
    mterpri() |> ignore
  }
  set(q_ccol, Fix(1L)) |> ignore
  myindent()
}

///|
/// lastelementp checks that there is only one element left in the list.
fn lastelementp(l : Value) -> Value raise {
  lbool(length(l) == 1)
}

///|
/// getsymbol gets the symbol of an atom from the database.
fn getsymbol(atom_ : Value) -> Value raise {
  get(atom_, q_chchr)
}

///|
/// setup builds the database (puts properties) for each key word.
fn setup(arg : Value) -> Value raise {
  for ls in cdr(arg).iter() {
    putprop(car(arg), cadr(ls), car(ls)) |> ignore
  }
  cdr(arg)
}

///|
/// mPr-lbp and mPr-rbp give the binding powers of an operator.
fn mpr_lbp(x : Value) -> Value raise {
  let v = get(x, q_mpr_lbp)
  if v.truthy() {
    v
  } else {
    lbp(x)
  }
}

///|
fn mpr_rbp(x : Value) -> Value raise {
  let v = get(x, q_mpr_rbp)
  if v.truthy() {
    v
  } else {
    rbp(x)
  }
}

///|
/// reduce lbp and rbp value for mtimes to get less parenthesis
fn d_lessparen() -> Value raise {
  putprop(q_mtimes, Fix(110L), q_mpr_lbp) |> ignore
  putprop(q_mtimes, Fix(110L), q_mpr_rbp) |> ignore
  q_d_done
}

///|
/// get back to normal case for paren
fn d_parenback() -> Value raise {
  putprop(q_mtimes, Fix(120L), q_mpr_lbp) |> ignore
  putprop(q_mtimes, Fix(120L), q_mpr_rbp) |> ignore
  q_d_done
}

///|
fn share_prmathml__t(s : String) -> Unit raise {
  tprinc(Str(s)) |> ignore
}

///|
/// mPr-abs handles abs()
fn mpr_abs(mexpress : Value) -> Value raise {
  share_prmathml__t("<mo>|</mo>")
  mpr_engine(cadr(mexpress), q_mparen, q_mparen) |> ignore
  tprinc(Str("<mo>|</mo>"))
}

///|
fn mpr_conjugate(mexpress : Value) -> Value raise {
  share_prmathml__t("<mover>")
  share_prmathml__t("<mrow>")
  mpr_engine(cadr(mexpress), q_mparen, q_mparen) |> ignore
  share_prmathml__t("</mrow>")
  share_prmathml__t("<mo>&#xaf;</mo>") // macron
  tprinc(Str("</mover>"))
}

///|
/// a[1]^2 or a[x,y]^z
fn mpr_arr_power(b : Value, e : Value) -> Value raise {
  share_prmathml__t("<msubsup>")
  mpr_engine(caar(b), symval(q_lop), q_mfunction) |> ignore
  if length(b) == 2 {
    mpr_engine(cadr(b), symval(q_lop), symval(q_rop)) |> ignore
  } else {
    row_begin(Str("<mrow>")) |> ignore
    let mut l = cdr(b)
    while l.truthy() {
      mpr_engine(car(l), symval(q_lop), symval(q_rop)) |> ignore
      if !lastelementp(l).truthy() {
        share_prmathml__t("<mo>,</mo>")
      }
      l = cdr(l)
    }
    row_end(Str("</mrow>")) |> ignore
  }
  mpr_engine(e, q_mparen, q_mparen) |> ignore
  tprinc(Str("</msubsup>"))
}

///|
/// when the operator is array, this function will be called
/// ex. a[x1,..] is a top level representation
fn mpr_array(mexpress : Value) -> Value raise {
  share_prmathml__t("<msub>")
  mpr_engine(caar(mexpress), symval(q_lop), q_mfunction) |> ignore
  row_begin(Str("<mrow>")) |> ignore
  let mut l = cdr(mexpress)
  while l.truthy() {
    mpr_engine(car(l), symval(q_lop), symval(q_rop)) |> ignore
    if !lastelementp(l).truthy() {
      share_prmathml__t("<mo>,</mo>")
    }
    l = cdr(l)
  }
  row_end(Str("</mrow>")) |> ignore
  tprinc(Str("</msub>"))
}

///|
/// mPr-at handles the at(..) function
fn mpr_at(mexpress : Value) -> Value raise {
  row_begin(Str("<mrow>")) |> ignore
  mpr_engine(cadr(mexpress), symval(q_lop), symval(q_rop)) |> ignore
  share_prmathml__t("<msub><mo>|</mo>")
  mpr_engine(caddr(mexpress), q_mparen, q_mparen) |> ignore
  share_prmathml__t("</msub>")
  row_end(Str("</mrow>"))
}

///|
/// e.g. 'at_difference(f(x), x, a, b)
fn mpr_at_difference(mexpress : Value) -> Value raise {
  let f = car(cdr(mexpress))
  let x = cadr(cdr(mexpress))
  let a = caddr(cdr(mexpress))
  let b = cadddr(cdr(mexpress))
  row_begin(Str("<mrow>")) |> ignore
  mpr_engine(f, symval(q_lop), symval(q_rop)) |> ignore
  share_prmathml__t("<msubsup><mo>|</mo>")
  mpr_engine(mk(q_mequal, [x, a]), q_mparen, q_mparen) |> ignore
  mpr_engine(mk(q_mequal, [x, b]), q_mparen, q_mparen) |> ignore
  share_prmathml__t("</msubsup>")
  row_end(Str("</mrow>"))
}

///|
/// COERCE of a list of characters and strings to a string: CL signals a
/// type error for the strings.
fn share_prmathml__coerce_chars(l : Value) -> Value raise {
  let sb = StringBuilder::new()
  for c in l.iter() {
    match c {
      Char(ch) => sb.write_char(ch)
      _ =>
        raise LispError::SimpleError(
          "The value " + prin1_to_string(c) + " is not of type CHARACTER",
        )
    }
  }
  Str(sb.to_string())
}

///|
/// whenever mexpress is an atom this function takes care of it, getting
/// its symbol if it exists; it also handles reserved characters.
fn mpr_atom(chr : Value) -> Value raise {
  if numberp(chr) {
    mpr_num(chr)
  } else if safe_get(chr, q_chchr).truthy() {
    share_prmathml__t("<mi>")
    tprinc(safe_get(chr, q_chchr)) |> ignore
    tprinc(Str("</mi>"))
  } else {
    let my_atom = if symbolp(chr) {
      print_invert_case(stripdollar(chr))
    } else {
      chr
    }
    share_prmathml__t("<mi>")
    tprinc(
      share_prmathml__coerce_chars(mapcar(c => handle_rsw(c), exploden(my_atom))),
    )
    |> ignore
    tprinc(Str("</mi>"))
  }
}

///|
fn rm(a : Value, list_ : Value) -> Value raise {
  let mut l = list_
  let mut l2 : Value = Nil
  while l.truthy() {
    if !equal(a, car(l)) {
      l2 = cons(car(l), l2)
    }
    l = cdr(l)
  }
  reverse(l2)
}

///|
/// called by mPr-atom, it checks for a reserved char.
fn handle_rsw(c : Value) -> Value raise {
  if equal(c, Char('<')) {
    Str("&lt;")
  } else if equal(c, Char('>')) {
    Str("&gt;")
  } else if equal(c, Char('&')) {
    Str("&amp;")
  } else {
    c
  }
}

///|
/// binomial coefficients (the second definition in PrMathML.lisp, which
/// replaces the first).
fn mpr_binomial(mexpress : Value) -> Value raise {
  row_begin(
    Str(
      "<mrow><mfenced open='(' close=')'><mfrac linethickness='0'><mrow>",
    ),
  )
  |> ignore
  mpr_engine(cadr(mexpress), q_mparen, q_mparen) |> ignore
  share_prmathml__t("</mrow><mrow>")
  mpr_engine(caddr(mexpress), q_mparen, q_mparen) |> ignore
  row_end(Str("</mrow></mfrac></mfenced></mrow>"))
}

///|
/// mPr-det handles determinant()
fn mpr_det(mexpress : Value) -> Value raise {
  let operand = cadr(mexpress)
  share_prmathml__t("<mi>det</mi>")
  mpr_engine(operand, q_mparen, q_mparen)
}

///|
/// mPr-diff handles the differentiation function. It calls powerof_d and
/// denopart.
fn mpr_diff(mexpress : Value) -> Value raise {
  if powerof_d(cddr(mexpress)).truthy() {
    denopart(cddr(mexpress)) |> ignore
    share_prmathml__t("</mfrac><mo>&InvisibleTimes;</mo>")
    mpr_engine(cadr(mexpress), q_mtimes, symval(q_rop)) |> ignore
    row_end(Str("</mrow>"))
  } else {
    mpr_engine(cadr(mexpress), symval(q_lop), symval(q_rop))
  }
}

///|
/// if there is no repeating differentiation, just diff(exp,x);
/// else diff(exp,x,no,..)
fn powerof_d(l : Value) -> Value raise {
  if lastelementp(l).truthy() {
    row_begin(Str("<mrow>")) |> ignore
    share_prmathml__t("<mfrac><mo> &dd; </mo>")
    return t
  }
  let mut l1 = l
  let mut l2 : Value = Nil
  while l1.truthy() {
    l2 = cons(cadr(l1), l2)
    l1 = cddr(l1)
  }
  let power_of_d = addn(l2, Nil)
  if numberp(power_of_d) {
    if equal(Fix(0L), power_of_d) {
      Nil
    } else if equal(Fix(1L), power_of_d) {
      row_begin(Str("<mrow>")) |> ignore
      share_prmathml__t("<mfrac><mo> &dd; </mo>")
      t
    } else {
      row_begin(Str("<mrow>")) |> ignore
      share_prmathml__t("<mfrac><msup><mo> &dd;</mo><mn>")
      tprinc(power_of_d) |> ignore
      share_prmathml__t("</mn></msup>")
      t
    }
  } else {
    row_begin(Str("<mrow>")) |> ignore
    share_prmathml__t("<mfrac><msup><mo> &dd;</mo>")
    mpr_engine(power_of_d, q_mparen, q_mparen) |> ignore
    share_prmathml__t("</msup>")
    t
  }
}

///|
/// if just diff(exp,x); if diff(exp,x,nox,y,noy,...)
fn denopart(l : Value) -> Value raise {
  if lastelementp(l).truthy() {
    row_begin(Str("<mrow>")) |> ignore
    share_prmathml__t("<mo> &dd; </mo>")
    p__op(getsymbol(q_mtimes)) |> ignore
    mpr_engine(car(l), q_mtimes, symval(q_rop)) |> ignore
    row_end(Str("</mrow>")) |> ignore
  } else {
    let mut l1 = l
    let mut l2 : Value = Nil
    while l1.truthy() {
      l2 = cons(list([list1(q_mexpt), car(l1), cadr(l1)]), l2)
      l1 = cddr(l1)
    }
    let result = muln(l2, Nil)
    if atom(result) {
      row_begin(Str("<mrow>")) |> ignore
      share_prmathml__t("<mo> &dd; </mo>")
      p__op(getsymbol(q_mtimes)) |> ignore
      mpr_engine(result, q_mparen, q_mparen) |> ignore
      row_end(Str("</mrow>")) |> ignore
    } else if listp(result) {
      if eq(caar(result), q_mexpt) {
        row_begin(Str("<mrow>")) |> ignore
        share_prmathml__t("<mo> &dd; </mo>")
        p__op(getsymbol(q_mtimes)) |> ignore
        mpr_engine(result, q_mtimes, q_mparen) |> ignore
        row_end(Str("</mrow>")) |> ignore
      } else {
        row_begin(Str("<mrow>")) |> ignore
        let mut l1 = cdr(result)
        while l1.truthy() {
          share_prmathml__t("<mo> &dd; </mo>")
          p__op(getsymbol(q_mtimes)) |> ignore
          mpr_engine(car(l1), q_mtimes, q_mtimes) |> ignore
          if !lastelementp(l1).truthy() {
            share_prmathml__t("<mo>,</mo>")
          }
          l1 = cdr(l1)
        }
        row_end(Str("</mrow>")) |> ignore
      }
    }
  }
  Nil
}

///|
/// Adopted from mactex's tex-mexpt (Richard Fateman). Insert
/// left-angle-brackets for mncexpt: a^<n> is how a^^n looks. f(x)^b is
/// displayed as f^b(x), as is the case for sin(x)^2, which should be
/// sin^2 x rather than (sin x)^2 or (sin(x))^2.
fn mpr_expt(mexpress : Value) -> Value raise {
  if eq(caar(mexpress), q_mexpt) {
    if !atom(cadr(mexpress)) && memq(q_array, caadr(mexpress)).truthy() {
      // array
      mpr_arr_power(cadr(mexpress), caddr(mexpress))
    } else {
      let fx = cadr(mexpress) // this is f(x)
      let f = if !atom(fx) && atom(caar(fx)) { caar(fx) } else { Nil } // this is f [or nil]
      let bascdr = if f.truthy() { cdr(fx) } else { Nil } // this is (x) [maybe (x,y..), or nil]
      let expon = caddr(mexpress) // this is the exponent
      let doit = f.truthy() && // there is such a function
        (match char_at(lstring(string(f)), 0) {
          '%' | '$' => true
          _ => false
        }) && // insist it is a % or $ function
        memq(f, list([q_p_sum, q_p_product])) is Nil
      if doit {
        if atom(expon) {
          // sin^2 x case
          row_begin(Str("<mrow>")) |> ignore
          share_prmathml__t("<msup>")
          mpr_fname(f) |> ignore
          mpr_atom(expon) |> ignore
          share_prmathml__t("</msup>")
          share_prmathml__t("<mo>&ApplyFunction;</mo>")
          if cdr(bascdr).truthy() {
            mpr_listparen(bascdr) |> ignore
          } else {
            mpr_engine(car(bascdr), q_mtimes, q_mtimes) |> ignore
          }
          row_end(Str("</mrow>"))
        } else {
          share_prmathml__t("<msup>")
          mpr_engine(fx, q_mparen, q_mparen) |> ignore
          mpr_engine(expon, q_mparen, q_mparen) |> ignore
          tprinc(Str("</msup>"))
        }
      } else {
        share_prmathml__t("<msup>")
        mpr_engine(cadr(mexpress), symval(q_lop), caar(mexpress)) |> ignore
        mpr_engine(caddr(mexpress), q_mparen, q_mparen) |> ignore
        tprinc(Str("</msup>"))
      }
    }
  } else {
    // mncexpt case
    share_prmathml__t("<msup>")
    mpr_engine(cadr(mexpress), symval(q_lop), caar(mexpress)) |> ignore
    row_begin(Str("<mrow>")) |> ignore
    share_prmathml__t("<mo>&LeftAngleBracket;</mo>")
    mpr_engine(caddr(mexpress), q_mparen, q_mparen) |> ignore
    share_prmathml__t("<mo>&RightAngleBracket;</mo>")
    row_end(Str("</mrow>")) |> ignore
    tprinc(Str("</msup>"))
  }
}

///|
/// prints the symbol of a function name from the database, or the name.
fn mpr_fname(f : Value) -> Value raise {
  share_prmathml__t("<mi>")
  tprinc(if getsymbol(f).truthy() { getsymbol(f) } else { f }) |> ignore
  tprinc(Str("</mi>"))
}

///|
/// to handle an operator which is a function
fn mpr_function(mexpress : Value) -> Value raise {
  mpr_engine(caar(mexpress), q_mparen, q_mparen) |> ignore
  share_prmathml__t("<mo>&ApplyFunction;</mo>")
  mpr_listparen(cdr(mexpress))
}

///|
fn mpr_gamma(mexpress : Value) -> Value raise {
  // ensure big gamma instead of little gamma (CHCHR property)
  mpr_engine(sym("$Gamma"), q_mparen, q_mparen) |> ignore
  share_prmathml__t("<mo>&ApplyFunction;</mo>")
  mpr_listparen(cdr(mexpress))
}

///|
/// for infix operators; also handles a truncation in the expression (see
/// mPr-infix1). If -x or +x, call mPr-function.
fn mpr_infix(mexpress : Value) -> Value raise {
  let moperator = car(mexpress)
  let moperands = cdr(mexpress)
  if length(moperands) == 1 {
    mpr_function(mexpress)
  } else {
    row_begin(Str("<mrow>")) |> ignore
    mpr_engine(car(moperands), symval(q_lop), car(moperator)) |> ignore
    p__op_oprd(moperator, cadr(moperands)) |> ignore
    mpr_infix1(moperator, cddr(moperands)) |> ignore
    row_end(Str("</mrow>"))
  }
}

///|
fn mpr_infix1(moperator : Value, moperands : Value) -> Value raise {
  if moperands is Nil {
    if member_equal(q_trunc, moperator).truthy() {
      p__op(getsymbol(car(moperator))) |> ignore
      tprinc(Str("<mo>&TripleDot;</mo>"))
    } else {
      Nil
    }
  } else {
    p__op_oprd(moperator, car(moperands)) |> ignore
    mpr_infix1(moperator, cdr(moperands))
  }
}

///|
/// p-op-oprd prints an operator and an operand consecutively,
/// ex. + x when + is an infix op and x is the operand
fn p__op_oprd(moperator : Value, moperand : Value) -> Value raise {
  let op = car(moperator)
  if equal(op, q_mplus) {
    if listp(moperand) {
      if equal(caar(moperand), q_mminus) {
        share_prmathml__t("<mo>-</mo>")
        mpr_engine(cadr(moperand), q_mminus, symval(q_rop))
      } else {
        share_prmathml__t("<mo>+</mo>")
        mpr_engine(moperand, q_mplus, symval(q_rop))
      }
    } else {
      share_prmathml__t("<mo>+</mo>")
      mpr_atom(moperand)
    }
  } else {
    p__op(getsymbol(op)) |> ignore
    mpr_engine(moperand, op, op)
  }
}

///|
fn p__op(symbol : Value) -> Value raise {
  share_prmathml__t("<mo>")
  tprinc(symbol) |> ignore
  tprinc(Str("</mo>"))
}

///|
/// ($substitute -inf minf e), evaluated
fn share_prmathml__subst_minf(e : Value) -> Value raise {
  meval(
    list([
      list1(q_d_substitute),
      mk(q_mminus, [q_d_inf]),
      q_d_minf,
      e,
    ]),
  )
}

///|
/// mPr-integrate handles an integration expression, in short form or long
/// form (example: integrate(x^4,x,0,inf) is a long form).
fn mpr_integrate(mexpress : Value) -> Value raise {
  let mexpress = share_prmathml__subst_minf(mexpress)
  if length(mexpress) == 3 {
    row_begin(Str("<mrow>")) |> ignore
    share_prmathml__t("<mo>&Integral;</mo>")
  } else if length(mexpress) == 5 {
    row_begin(Str("<mrow>")) |> ignore
    share_prmathml__t("<msubsup><mo>&Integral;</mo>")
    row_begin(Str("<mrow>")) |> ignore
    mpr_engine(cadddr(mexpress), q_mparen, q_mparen) |> ignore
    row_end(Str("</mrow>")) |> ignore
    share_prmathml__t("  ")
    row_begin(Str("<mrow>")) |> ignore
    mpr_engine(car(cddddr(mexpress)), q_mparen, q_mparen) |> ignore
    row_end(Str("</mrow>")) |> ignore
    share_prmathml__t("</msubsup>")
  } else {
    merr("Wrong NO. of Arguments", []) |> ignore
  }
  row_begin(Str("<mrow>")) |> ignore
  mpr_engine(cadr(mexpress), q_mparen, q_mparen) |> ignore
  row_end(Str("</mrow>")) |> ignore
  share_prmathml__t("<mo>&InvisibleTimes;</mo><mo> &dd; </mo>")
  mpr_engine(caddr(mexpress), q_mparen, symval(q_rop)) |> ignore
  row_end(Str("</mrow>"))
}

///|
/// mPr-limit takes care of "limit(exp,var,val,dir)"
fn mpr_limit(mexpress : Value) -> Value raise {
  let mexpress = share_prmathml__subst_minf(mexpress)
  row_begin(Str("<mrow>")) |> ignore
  share_prmathml__t("<munder><mo>lim</mo>")
  row_begin(Str("<mrow>")) |> ignore
  mpr_engine(caddr(mexpress), q_mparen, q_mparen) |> ignore
  share_prmathml__t("<mo>&RightArrow;</mo>")
  mpr_engine(cadddr(mexpress), q_mparen, q_mapren) |> ignore
  let dir = car(cddddr(mexpress))
  if dir.truthy() {
    if member_equal(dir, list([q_d_minus, q_d_plus])).truthy() {
      p__op(getsymbol(dir)) |> ignore
    } else {
      merr("THE 4TH ARG MUST BE PLUS OR MINUS", []) |> ignore
    }
  }
  row_end(Str("</mrow>")) |> ignore
  share_prmathml__t("</munder>")
  mpr_engine(cadr(mexpress), q_mparen, symval(q_rop)) |> ignore
  row_end(Str("</mrow>"))
}

///|
/// handles a Maxima list expression
fn mpr_list(mexpress : Value) -> Value raise {
  share_prmathml__t("<mo>[</mo>")
  let mut l = cdr(mexpress)
  while l.truthy() {
    mpr_engine(car(l), q_mparen, q_mparen) |> ignore
    if !lastelementp(l).truthy() {
      share_prmathml__t("<mo>,</mo>")
    }
    l = cdr(l)
  }
  tprinc(Str("<mo>]</mo>"))
}

///|
/// a subfunction of mPr-expt, mPr-function and mPr-mqapply
fn mpr_listparen(mexpress : Value) -> Value raise {
  row_begin(Str("<mrow>")) |> ignore
  share_prmathml__t("<mo>(</mo>")
  let mut l = mexpress
  while l.truthy() {
    mpr_engine(car(l), q_mparen, q_mparen) |> ignore
    if !lastelementp(l).truthy() {
      share_prmathml__t("<mo>,</mo>")
    }
    l = cdr(l)
  }
  share_prmathml__t("<mo>)</mo>")
  row_end(Str("</mrow>"))
}

///|
/// mPr-matrix handles the matrix function
fn mpr_matrix(mexpress : Value) -> Value raise {
  row_begin(Str("<mfenced open='(' close=')'><mtable>")) |> ignore
  for arg_ in cdr(mexpress).iter() {
    row_begin(Str("<mtr>")) |> ignore
    let mut l = cdr(arg_)
    while l.truthy() {
      row_begin(Str("<mtd>")) |> ignore
      mpr_engine(car(l), q_mparen, q_mparen) |> ignore
      row_end(Str("</mtd>")) |> ignore
      l = cdr(l)
    }
    row_end(Str("</mtr>")) |> ignore
  }
  row_end(Str("</mtable></mfenced>"))
}

///|
fn mpr_mqapply(mexpress : Value) -> Value raise {
  mpr_engine(cadr(mexpress), symval(q_lop), q_mfunction) |> ignore
  mpr_listparen(cddr(mexpress))
}

///|
/// handles floating point numbers: convert 1.2e20 to 1.2 \cdot 10^{20}
fn mpr_num(atom_ : Value) -> Value raise {
  if integerp(atom_) {
    share_prmathml__t("<mn>")
    tprinc(atom_) |> ignore
    return tprinc(Str("</mn>"))
  }
  let r = exploden(atom_)
  let exponent = {
    let e = member(Char('e'), r)
    if e.truthy() {
      e
    } else {
      member(Char('E'), r)
    }
  }
  if exponent is Nil {
    // it is not. go with it as given
    share_prmathml__t("<mn>")
    tprinc(atom_) |> ignore
    tprinc(Str("</mn>"))
  } else {
    let rr = reverse(r)
    let m = {
      let e = member(Char('e'), rr)
      if e.truthy() {
        e
      } else {
        member(Char('E'), rr)
      }
    }
    let firstpart = nreverse(cdr(m))
    share_prmathml__t("<mn>")
    for c in firstpart.iter() {
      tpchar(c) |> ignore
    }
    share_prmathml__t("</mn>")
    share_prmathml__t("<mo>&CenterDot;</mo><msup><mn>10</mn> <mn>")
    for c in cdr(exponent).iter() {
      tpchar(c) |> ignore
    }
    tprinc(Str("</mn></msup>"))
  }
}

///|
/// this function puts parenthesis around the expression
fn mpr_paren(mexpress : Value) -> Value raise {
  row_begin(Str("<mrow>")) |> ignore
  share_prmathml__t("<mo>(</mo>")
  mpr_engine(mexpress, q_mparen, q_mparen) |> ignore
  share_prmathml__t("<mo>)</mo>")
  row_end(Str("</mrow>"))
}

///|
/// handles the "+" operator, which is infix. If -x or +x, call
/// mPr-prefix.
fn mpr_plus(mexpress : Value) -> Value raise {
  let moperands = cdr(mexpress)
  let flag_trunc = memq(q_trunc, car(mexpress))
  if length(moperands) == 1 {
    mpr_prefix(mexpress)
  } else {
    row_begin(Str("<mrow>")) |> ignore
    mpr_engine(car(moperands), symval(q_lop), q_mplus) |> ignore
    print_op_oprd(cadr(moperands)) |> ignore
    mpr_plus1(cddr(moperands), flag_trunc) |> ignore
    row_end(Str("</mrow>"))
  }
}

///|
fn mpr_plus1(moperands : Value, flag_trunc : Value) -> Value raise {
  if moperands is Nil {
    if flag_trunc.truthy() {
      tprinc(Str("<mo>+</mo><mo>&TripleDot;</mo>"))
    } else {
      Nil
    }
  } else {
    print_op_oprd(car(moperands)) |> ignore
    mpr_plus1(cdr(moperands), flag_trunc)
  }
}

///|
fn print_op_oprd(moperand : Value) -> Value raise {
  if listp(moperand) {
    if equal(caar(moperand), q_mminus) {
      share_prmathml__t("<mo>-</mo>")
      mpr_engine(cadr(moperand), q_mplus, symval(q_rop))
    } else {
      share_prmathml__t("<mo>+</mo>")
      mpr_engine(moperand, q_mplus, q_mparen)
    }
  } else {
    share_prmathml__t("<mo>+</mo>")
    mpr_atom(moperand)
  }
}

///|
/// mPr-postfix handles postfix notation expressions like factorial
fn mpr_postfix(mexpress : Value) -> Value raise {
  row_begin(Str("<mrow>")) |> ignore
  mpr_engine(cadr(mexpress), symval(q_lop), caar(mexpress)) |> ignore
  row_end(Str("</mrow>")) |> ignore
  p__op(getsymbol(caar(mexpress)))
}

///|
/// mPr-prefix handles a prefix notation form
fn mpr_prefix(mexpress : Value) -> Value raise {
  let op = caar(mexpress)
  let oprnd = cadr(mexpress)
  row_begin(Str("<mrow>")) |> ignore
  p__op(getsymbol(op)) |> ignore
  mpr_engine(oprnd, op, symval(q_rop)) |> ignore
  row_end(Str("</mrow>"))
}

///|
/// this function takes care of the quotient function or "/" sign
fn mpr_quotient(mexpress : Value) -> Value raise {
  row_begin(Str("<mfrac><mrow>")) |> ignore
  mpr_engine(cadr(mexpress), q_mparen, q_mparen) |> ignore
  row_end(Str("</mrow>")) |> ignore
  row_begin(Str("<mrow>")) |> ignore
  mpr_engine(caddr(mexpress), q_mparen, q_mparen) |> ignore
  row_end(Str("</mrow></mfrac>"))
}

///|
fn mpr_rat(mexpress : Value) -> Value raise {
  mpr_quotient(mexpress)
}

///|
/// this function handles sqrt
fn mpr_sqrt(mexpress : Value) -> Value raise {
  share_prmathml__t("<msqrt>")
  mpr_engine(cadr(mexpress), q_mparen, q_mparen) |> ignore
  tprinc(Str("</msqrt>"))
}

///|
/// This function takes care of both sum(exp,ind,lo,hi) and
/// product(exp,ind,lo,hi)
fn mpr_sumprod(mexpress : Value) -> Value raise {
  row_begin(Str("<mrow>")) |> ignore
  share_prmathml__t("<munderover>")
  p__op(getsymbol(caar(mexpress))) |> ignore
  row_begin(Str("<mrow>")) |> ignore
  mpr_engine(caddr(mexpress), q_mparen, q_mequal) |> ignore
  share_prmathml__t("<mo>=</mo>")
  mpr_engine(share_prmathml__subst_minf(cadddr(mexpress)), q_mequal, q_mparen)
  |> ignore
  row_end(Str("</mrow>")) |> ignore
  mpr_engine(
    share_prmathml__subst_minf(car(cddddr(mexpress))),
    q_mparen,
    q_mparen,
  )
  |> ignore
  share_prmathml__t("</munderover>")
  mpr_engine(cadr(mexpress), q_mparen, symval(q_rop)) |> ignore
  row_end(Str("</mrow>"))
}

///|
/// mPr-times handles multiplication
fn mpr_times(mexpress : Value) -> Value raise {
  with_specials([(q_lop, q_mtimes), (q_rop, q_mtimes)], () => mpr_infix(
    mexpress,
  ))
}

///|
fn mathml_presentation_lambda(mexpress : Value) -> Value raise {
  let op = caar(mexpress)
  let args = cdr(cadr(mexpress))
  let body = cddr(mexpress)
  mpr_engine(op, q_mparen, q_mparen) |> ignore
  if length(args) == 1 {
    mpr_engine(car(args), q_mparen, q_mparen) |> ignore
  } else {
    mpr_listparen(args) |> ignore
  }
  mpr_engine(Str("."), q_mparen, q_mparen) |> ignore
  if length(body) == 1 {
    mpr_engine(car(body), q_mparen, q_mparen)
  } else {
    mpr_listparen(body)
  }
}

///|
/// An improvement on the default, but not much.
fn mathml_presentation_buildinfo(mexpress : Value) -> Value raise {
  mpr_engine(
    cons(list1(q_d_matrix), mapcar(e => list([list1(q_mlist), e]), cdr(mexpress))),
    q_mparen,
    q_mparen,
  )
}

///|
/// (setup '(name (prop value) ...))
fn share_prmathml__setup(name : Value, props : Array[(Value, Value)]) -> Unit raise {
  setup(cons(name, list(props.map(p => list([p.0, p.1]))))) |> ignore
}

///|
fn init_share_n_cp_r_cm_ath_cm__cl_() -> Unit raise {
  let s = (x : String) => Value::Str(x)
  let pr = q_mprprocess
  let lb = q_mpr_lbp
  let rb = q_mpr_rbp
  let ch = q_chchr
  let f = (x : Int) => Value::Fix(x.to_int64())
  // Operators
  share_prmathml__setup(q_mlist, [(pr, q_mpr_list)])
  share_prmathml__setup(q_mplus, [
    (pr, q_mpr_plus),
    (lb, f(100)),
    (rb, f(100)),
    (ch, s("+")),
  ])
  share_prmathml__setup(q_mminus, [
    (pr, q_mpr_prefix),
    (lb, f(100)),
    (rb, f(100)),
    (ch, s("-")),
  ])
  share_prmathml__setup(q_mquote, [(pr, q_mpr_prefix), (rb, f(201)), (ch, s("'"))])
  share_prmathml__setup(q_mand, [
    (pr, q_mpr_infix),
    (lb, f(60)),
    (rb, f(60)),
    (ch, s("and")),
  ])
  share_prmathml__setup(q_mor, [
    (pr, q_mpr_infix),
    (lb, f(50)),
    (rb, f(50)),
    (ch, s("or")),
  ])
  share_prmathml__setup(q_mnot, [(pr, q_mpr_prefix), (rb, f(70)), (ch, s("&not;"))])
  let infix80 : Array[(Value, String)] = [
    (q_mgreaterp, "&gt;"),
    (q_mgeqp, "&ge;"),
    (q_mnotequal, "&NotEqual;"),
    (q_mleqp, "&le;"),
    (q_mlessp, "&lt;"),
  ]
  for e in infix80 {
    share_prmathml__setup(e.0, [
      (pr, q_mpr_infix),
      (lb, f(80)),
      (rb, f(80)),
      (ch, s(e.1)),
    ])
  }
  share_prmathml__setup(q_msetq, [
    (pr, q_mpr_infix),
    (lb, f(180)),
    (rb, f(20)),
    (ch, s("&Assign;")),
  ])
  share_prmathml__setup(q_mset, [
    (pr, q_mpr_infix),
    (lb, f(180)),
    (rb, f(20)),
    (ch, s("&Assign;")),
  ]) // This is not math
  share_prmathml__setup(q_mdefine, [
    (pr, q_mpr_infix),
    (lb, f(180)),
    (rb, f(20)),
    (ch, s(":=")),
  ])
  share_prmathml__setup(q_mfactorial, [
    (pr, q_mpr_postfix),
    (lb, f(160)),
    (ch, s("!")),
  ])
  share_prmathml__setup(q_mabs, [(pr, q_mpr_abs)])
  share_prmathml__setup(q_p_abs, [(pr, q_mpr_abs)])
  share_prmathml__setup(q_d_conjugate, [(pr, q_mpr_conjugate)])
  share_prmathml__setup(q_mnctimes, [
    (pr, q_mpr_infix),
    (lb, f(110)),
    (rb, f(109)),
    (ch, s("&CenterDot;")),
  ])
  share_prmathml__setup(q_marrow, [
    (pr, q_mpr_infix),
    (lb, f(180)),
    (rb, f(20)),
    (ch, s("&RightArrow;")),
  ])
  share_prmathml__setup(q_mrarrow, [
    (pr, q_mpr_prefix),
    (lb, f(180)),
    (rb, f(20)),
    (ch, s("&RightArrow;")),
  ])
  share_prmathml__setup(q_mdif, [
    (pr, q_mpr_infix),
    (lb, f(100)),
    (rb, f(100)),
    (ch, s("-")),
  ])
  share_prmathml__setup(q_mtimes, [
    (pr, q_mpr_times),
    (lb, f(120)),
    (rb, f(120)),
    (ch, s("&InvisibleTimes;")),
  ])
  share_prmathml__setup(q_mdottimes, [
    (pr, q_mpr_infix),
    (lb, f(120)),
    (rb, f(120)),
    (ch, s("&CenterDot;")),
  ])
  share_prmathml__setup(q_mexpt, [(pr, q_mpr_expt), (lb, f(140)), (rb, f(139))])
  share_prmathml__setup(q_mncexpt, [(pr, q_mpr_expt), (lb, f(135)), (rb, f(134))])
  share_prmathml__setup(q_p_at, [(pr, q_mpr_at)])
  share_prmathml__setup(q_d_at, [(pr, q_mpr_at)])
  share_prmathml__setup(q_p_at_difference, [(pr, q_mpr_at_difference)])
  share_prmathml__setup(sym("$det"), [(pr, q_mpr_det)])
  share_prmathml__setup(q_p_determinant, [(pr, q_mpr_det)])
  share_prmathml__setup(q_d_binomial, [(pr, q_mpr_binomial)])
  share_prmathml__setup(q_p_binomial, [(pr, q_mpr_binomial)])
  share_prmathml__setup(q_p_sum, [(pr, q_mpr_sumprod), (ch, s("&Sum;"))])
  share_prmathml__setup(q_d_sum, [(pr, q_mpr_sumprod), (ch, s("&Sum;"))])
  share_prmathml__setup(q_d_product, [(pr, q_mpr_sumprod), (ch, s("&Prod;"))])
  share_prmathml__setup(q_p_product, [(pr, q_mpr_sumprod), (ch, s("&Prod;"))])
  share_prmathml__setup(q_d_integrate, [
    (pr, q_mpr_integrate),
    (ch, s("&Integral;")),
  ])
  share_prmathml__setup(q_p_integrate, [
    (pr, q_mpr_integrate),
    (ch, s("&Integral;")),
  ])
  share_prmathml__setup(q_d_diff, [(pr, q_mpr_diff), (ch, s("<mo>&dd;</mo>"))])
  share_prmathml__setup(q_p_derivative, [
    (pr, q_mpr_diff),
    (ch, s("<mo>&dd;</mo>")),
  ])
  share_prmathml__setup(q_d_limit, [(pr, q_mpr_limit)])
  share_prmathml__setup(q_p_limit, [(pr, q_mpr_limit)])
  share_prmathml__setup(q_d_sqrt, [(pr, q_mpr_sqrt), (ch, s("&Sqrt;"))])
  share_prmathml__setup(q_p_sqrt, [(pr, q_mpr_sqrt), (ch, s("&Sqrt;"))])
  share_prmathml__setup(q_p_binomial, [(pr, q_mpr_binomial)])
  share_prmathml__setup(q_mquotient, [
    (pr, q_mpr_quotient),
    (lb, f(122)),
    (rb, f(123)),
    (ch, s("<mo>/</mo>")),
  ])
  share_prmathml__setup(q_rat, [(pr, q_mpr_rat), (lb, f(120)), (rb, f(121))])
  share_prmathml__setup(q_mconc, [(pr, q_mpr_infix), (ch, s(" "))])
  share_prmathml__setup(q_mparen, [(ch, s(" "))])
  share_prmathml__setup(q_mbrak, [(ch, s(" "))])
  share_prmathml__setup(q_mequal, [
    (pr, q_mpr_infix),
    (lb, f(80)),
    (rb, f(80)),
    (ch, s("=")),
  ])
  share_prmathml__setup(q_mqapply, [(pr, q_mpr_mqapply)])
  share_prmathml__setup(q_mmfunct, [(pr, q_mpr_funct)])
  share_prmathml__setup(q_d_matrix, [(pr, q_mpr_matrix)])
  share_prmathml__setup(q_lambda, [(pr, q_mathml_presentation_lambda)])
  share_prmathml__setup(q_p_build_info, [(pr, q_mathml_presentation_buildinfo)])
  let chchrs : Array[(Value, String)] = [
    (q_d__pctpi, "&pi;"),
    (q_d__pcte, "&ee;"),
    (sym("$%gamma"), "&gamma;"),
    (sym("$%phi"), "&phi;"),
    (sym("&"), "&amp;"),
    (sym("%"), "%"),
    (sym("$"), "$"),
    (sym("_"), "_"),
    (q_d_minus, "-"),
    (q_d_plus, "+"),
    (q_mprog, "block"),
    (sym("$$block"), "block"),
    (sym("$$boldif"), "if"),
    (sym("$$boldthen"), "then"),
    (sym("$$boldelse"), "else"),
  ]
  for e in chchrs {
    share_prmathml__setup(e.0, [(ch, s(e.1))])
  }
  // The following are databases for special characters
  let specials : Array[(String, String)] = [
    ("$inf", "&infin;"),
    // lower case greek database
    ("$alpha", "&alpha;"),
    ("%alpha", "&alpha;"),
    ("$beta", "&beta;"),
    ("$gamma", "&gamma;"),
    ("%gamma", "&gamma;"),
    ("%gamma_incomplete", "&Gamma;"),
    ("%gamma_incomplete_generalized", "&Gamma;"),
    ("%gamma_incomplete_regularized", "Q"),
    ("$gamma_incomplete_lower", "&gamma;"),
    ("$delta", "&delta;"),
    ("$epsilon", "&epsilon;"),
    ("$varepsilon", "&varepsilon;"),
    ("$zeta", "&zeta;"),
    ("$eta", "&eta;"),
    ("$theta", "&theta;"),
    ("$vartheta", "&vartheta;"),
    ("$iota", "&iota;"),
    ("$kappa", "&kappa;"),
    ("$lambda", "&lambda;"),
    ("lambda", "&lambda;"),
    ("$mu", "&mu;"),
    ("$nu", "&nu;"),
    ("$xi", "&xi;"),
    ("$pi", "&pi;"),
    ("$varpi", "&varpi;"),
    ("$rho", "&rho;"),
    ("$varrho", "&varrho;"),
    ("$sigma", "&sigma;"),
    ("$varsigma", "&varsigma;"),
    ("$tau", "&tau;"),
    ("$upsilon", "&upsilon;"),
    ("$phi", "&phi;"),
    ("$varphi", "&varphi;"),
    ("$chi", "&chi;"),
    ("$psi", "&psi;"),
    ("$omega", "&omega;"),
    // Greek Upper Case Database
    ("$Alpha", "&Alpha;"),
    ("$Gamma", "&Gamma;"),
    ("$Delta", "&Delta;"),
    ("$Theta", "&Theta;"),
    ("$Lambda", "&Lambda;"),
    ("$Xi", "&Xi;"),
    ("$Pi", "&Pi;"),
    ("$Sigma", "&Sigma;"),
    ("$Upsilon", "&Upsilon;"),
    ("$Phi", "&Phi;"),
    ("$Psi", "&Psi;"),
    ("$Omega", "&Omega;"),
    ("$Re", "&Re;"),
    ("$Im", "&Im;"),
    // Miscellaneous symbols
    ("$aleph", "&aleph;"),
    ("$hbar", "&hbar;"),
    ("$%i", "&ii;"),
    ("$%j", "&ij"),
    ("$ell", "&ell;"),
    ("$wp", "&wp;"),
    ("$mho", "&mho;"),
    ("$infty", "&infty;"),
    ("$nabla", "&nabla;"),
    ("$partial", "&PartialD;"),
    ("$triangle", "&triangle;"),
  ]
  for e in specials {
    putprop(sym(e.0), s(e.1), ch) |> ignore
  }
  let fns : Array[(String, String)] = [
    ("sin", "sin"),
    ("cos", "cos"),
    ("tan", "tan"),
    ("cot", "cot"),
    ("sec", "sec"),
    ("csc", "csc"),
    ("asin", "arcsin"),
    ("acos", "arccos"),
    ("atan", "arctan"),
    ("acot", "acot"),
    ("asec", "asec"),
    ("acsc", "acsc"),
    ("sinh", "sinh"),
    ("cosh", "cosh"),
    ("tanh", "tanh"),
    ("coth", "coth"),
    ("sech", "sec"),
    ("csch", "csch"),
    ("asinh", "asinh"),
    ("acosh", "acosh"),
    ("atanh", "atanh"),
    ("acoth", "acoth"),
    ("asech", "asec"),
    ("acsch", "acsch"),
    ("ln", "ln"),
    ("log", "log"),
  ]
  for e in fns {
    share_prmathml__setup(sym("%" + e.0), [
      (pr, q_mpr_function),
      (rb, f(110)),
      (ch, s(e.1)),
    ])
  }
  for e in fns {
    share_prmathml__setup(sym("$" + e.0), [
      (pr, q_mpr_function),
      (rb, f(110)),
      (ch, s(e.1)),
    ])
  }
  share_prmathml__setup(q_p_gamma, [(pr, q_mpr_gamma)])
  // set the preference feature
  d_lessparen() |> ignore
  set(sym("casep"), Nil) |> ignore // set to distinguish a capital or lower case
  set(q_d_mprworksheet, Nil) |> ignore // set TeX worksheet mode false
  set(q_d_lamprworksheet, Nil) |> ignore // set LaTeX worksheet mode false
  set(q_d_mprlabelleft, Nil) |> ignore // set Tex or LaTeX left Labeling mode false
  set(q_d_mprdisplaytype, t) |> ignore // set default for TeX or LaTeX in display type
  set(q_d_mprevaluate, t) |> ignore // set default for evaluating macsyma expression
  set(q_d_mprautolabel, Nil) |> ignore // set autolabel mode off, can be set to be integer
  set(q_d_lamprautolabel, Nil) |> ignore // set LaTeX autolabel mode false
  // The MathML presentation code has been loaded. Run each post-load hook.
  // Each hook should be an idempotent thunk.
  if boundp(q_ear_mathml_presentation_hook) {
    for hook in symval(q_ear_mathml_presentation_hook).iter() {
      funcall(hook, []) |> ignore
    }
  }
}
