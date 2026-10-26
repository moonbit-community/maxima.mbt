// Port of share/contrib/maximaMathML/CtMathML.lisp: generate Content
// MathML code from Maxima (Paul S. Wang, Kent State University, 1999).
// Once loaded, use the command ctmathml(expr [,file]).

///|
fn d_ctmathml(margs : Value) -> Value raise {
  let mut filename : Value = Nil
  let mut file_path = ""
  with_specials(
    [
      (q_ccol, Fix(1L)),
      (q_ear_row, t),
      (share_prmathml__q_indent, Fix(0L)),
      (share_prmathml__q_mprport, Nil),
      (q_lop, q_mparen),
      (q_rop, q_mparen),
    ],
    () => {
      let mut mexpress = car(margs)
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
      tprinc(Str("<math  xmlns='http://www.w3.org/1998/Math/MathML'>")) |> ignore
      ctmathml(nformat(mexpress)) |> ignore // call engine
      tprinc(Str("</math>")) |> ignore
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
fn masymbol(op : Value, l : Value) -> Value raise {
  let ans = assoc(op, l)
  if ans.truthy() {
    cdr(ans)
  } else {
    Nil
  }
}

///|
fn mpsymbol(op : Value, l : Value) -> Value raise {
  if l is Nil {
    Nil
  } else if eq(op, cdar(l)) {
    caar(l)
  } else {
    mpsymbol(op, cdr(l))
  }
}

///|
fn ctmathml(exp_ : Value) -> Value raise {
  if atom(exp_) {
    a2ml(exp_) // atoms
  } else if fractionp(exp_).truthy() {
    Nil // fractional number
  } else if get(caar(exp_), q_ct_proc).truthy() {
    funcall(get(caar(exp_), q_ct_proc), [caar(exp_), cdr(exp_)])
  } else if get(caar(exp_), q_ctfun).truthy() {
    op2ml(caar(exp_), cdr(exp_)) // known function
  } else if memq(q_array, car(exp_)).truthy() {
    ctarray(exp_)
  } else if cpxp(exp_).truthy() {
    Nil // complex number
  } else {
    op2ml(caar(exp_), cdr(exp_))
  }
}

///|
fn op2ml(op : Value, args : Value) -> Value raise {
  let sym_ = get(op, q_ctfun)
  if sym_.truthy() {
    row_begin(Str("<apply>")) |> ignore
    share_prmathml__t("<")
    tprinc(sym_) |> ignore
    share_prmathml__t(">")
  } else {
    row_begin(Str("<apply>")) |> ignore
    share_prmathml__t("<fn>")
    tprinc(stripdollar(op)) |> ignore
    share_prmathml__t("</fn>")
  }
  for a in args.iter() {
    ctmathml(a) |> ignore
  }
  row_end(Str("</apply>"))
}

///|
/// subscripted var
fn ctarray(a : Value) -> Value raise {
  share_prmathml__t("<ci>")
  row_begin(Str("")) |> ignore
  mpr_array(a) |> ignore
  row_end(Str("")) |> ignore
  tprinc(Str("</ci>"))
}

///|
/// treat atoms
fn a2ml(a : Value) -> Value raise {
  if numberp(a) {
    share_prmathml__t("<cn")
    if fixnump(a) || bignump_(a).truthy() {
      share_prmathml__t(" type=\"integer\">")
    } else if floatp(a) || bigfloatp(a).truthy() {
      share_prmathml__t(" type=\"float\">")
    } else {
      share_prmathml__t(">")
    }
    tprinc(Str(princ_to_string(a))) |> ignore
    return tprinc(Str("</cn>"))
  }
  let val = safe_get(a, q_chchr)
  if val.truthy() {
    if member_equal(
        val,
        list([Str("&pi;"), Str("&gamma;"), Str("&ii;"), Str("&ee;")]),
      ).truthy() {
      share_prmathml__t("<cn type=\"constant\">")
    } else {
      share_prmathml__t("<cn>")
    }
    tprinc(val) |> ignore
    tprinc(Str("</cn>"))
  } else {
    let my_atom = if symbolp(a) { print_invert_case(stripdollar(a)) } else { a }
    share_prmathml__t("<ci>")
    tprinc(
      share_prmathml__coerce_chars(
        mapcar(c => handle_rsw(c), rm(sym("//"), exploden(my_atom))),
      ),
    )
    |> ignore
    tprinc(Str("</ci>"))
  }
}

///|
fn cpxp(a : Value) -> Value raise {
  if among(q_d__pcti, a).truthy() {
    let r = d_realpart(a)
    let i = d_imagpart(a)
    if numberp(r) && numberp(i) {
      share_prmathml__t("<cn type=\"complex\">")
      tprinc(r) |> ignore
      share_prmathml__t("<sep/>")
      tprinc(i) |> ignore
      share_prmathml__t("</cn>")
      t
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn fractionp(a : Value) -> Value raise {
  if eq(caar(a), q_rat) && integerp(cadr(a)) && integerp(caddr(a)) {
    share_prmathml__t("<cn type=\"rational\">")
    tprinc(cadr(a)) |> ignore
    share_prmathml__t("<sep/>")
    tprinc(caddr(a)) |> ignore
    share_prmathml__t("</cn>")
    t
  } else {
    Nil
  }
}

///|
fn ctlist(_op : Value, args : Value) -> Value raise {
  share_prmathml__t("<list>")
  for a in args.iter() {
    ctmathml(a) |> ignore
  }
  tprinc(Str("</list>"))
}

///|
fn ctset(_op : Value, args : Value) -> Value raise {
  share_prmathml__t("<set>")
  for a in args.iter() {
    ctmathml(a) |> ignore
  }
  tprinc(Str("</set>"))
}

///|
fn matrixrow(args : Value) -> Value raise {
  let args = cdr(args)
  row_begin(Str("<matrixrow>")) |> ignore
  for a in args.iter() {
    ctmathml(a) |> ignore
  }
  row_end(Str("</matrixrow>"))
}

///|
fn ctmatrix(_op : Value, args : Value) -> Value raise {
  row_begin(Str("<matrix>")) |> ignore
  for a in args.iter() {
    matrixrow(a) |> ignore
  }
  row_end(Str("</matrix>"))
}

///|
fn ctvector(_op : Value, args : Value) -> Value raise {
  share_prmathml__t("<vector>")
  for a in args.iter() {
    ctmathml(a) |> ignore
  }
  tprinc(Str("</vector>"))
}

///|
fn relation(op : Value, args : Value) -> Value raise {
  let sym_ = get(op, q_ctfun)
  row_begin(Str("<reln>")) |> ignore
  share_prmathml__t("<")
  tprinc(sym_) |> ignore
  share_prmathml__t(">")
  for a in args.iter() {
    ctmathml(a) |> ignore
  }
  row_end(Str("</reln>"))
}

///|
fn sumprod(op : Value, args : Value) -> Value raise {
  if length(args) == 4 {
    let sym_ = get(op, q_ctfun)
    let exp_ = car(args)
    let var_ = cadr(args)
    let ll = caddr(args)
    let ul = cadddr(args)
    row_begin(Str("<apply>")) |> ignore
    share_prmathml__t("<")
    tprinc(sym_) |> ignore
    share_prmathml__t(">")
    share_prmathml__t("<bvar>")
    ctmathml(var_) |> ignore
    share_prmathml__t("</bvar>")
    let ll = nformat(share_prmathml__subst_minf(ll))
    share_prmathml__t("<lowlimit>")
    ctmathml(ll) |> ignore
    share_prmathml__t("</lowlimit>")
    myterpri() |> ignore
    let ul = nformat(share_prmathml__subst_minf(ul))
    share_prmathml__t("<uplimit>")
    ctmathml(ul) |> ignore
    share_prmathml__t("</uplimit>")
    ctmathml(exp_) |> ignore
    row_end(Str("</apply>"))
  } else {
    tprinc(Str("sumprod: Wrong args"))
  }
}

///|
fn ctlimit(op : Value, args : Value) -> Value raise {
  let sym_ = get(op, q_ctfun)
  let f = car(args)
  let v = cadr(args)
  let p = caddr(args)
  let args = cdddr(args)
  row_begin(Str("<apply>")) |> ignore
  share_prmathml__t("<")
  tprinc(sym_) |> ignore
  share_prmathml__t(">")
  share_prmathml__t("<bvar>")
  ctmathml(v) |> ignore
  share_prmathml__t("</bvar>")
  let p = nformat(share_prmathml__subst_minf(p))
  share_prmathml__t("<lowlimit>")
  ctmathml(p) |> ignore
  share_prmathml__t("</lowlimit>")
  myterpri() |> ignore
  if args.truthy() {
    row_begin(Str("<condition>")) |> ignore
    // both directions are written as v > 0
    relation(q_mgreaterp, list([v, Fix(0L)])) |> ignore
    row_end(Str("</condition>")) |> ignore
  }
  ctmathml(f) |> ignore
  row_end(Str("</apply>"))
}

///|
fn ctdiff(op : Value, args : Value) -> Value raise {
  let sym_ = get(op, q_ctfun)
  let f = car(args)
  let args = cdr(args)
  row_begin(Str("<apply>")) |> ignore
  share_prmathml__t("<")
  tprinc(sym_) |> ignore
  share_prmathml__t(">")
  ctmathml(f) |> ignore
  if length(args) == 1 {
    share_prmathml__t("<bvar>")
    ctmathml(car(args)) |> ignore
    share_prmathml__t("</bvar>")
  } else {
    let mut vl = args
    while vl.truthy() {
      diffvar(car(vl), cadr(vl)) |> ignore
      vl = cddr(vl)
    }
  }
  row_end(Str("</apply>"))
}

///|
fn diffvar(v : Value, d : Value) -> Value raise {
  share_prmathml__t("<bvar>")
  ctmathml(v) |> ignore
  share_prmathml__t("<degree>")
  ctmathml(d) |> ignore
  share_prmathml__t("</degree>")
  share_prmathml__t("</bvar>")
  myterpri()
}

///|
fn ctintegrate(op : Value, args : Value) -> Value raise {
  if length(args) == 4 {
    sumprod(op, args)
  } else {
    let sym_ = get(op, q_ctfun)
    let exp_ = car(args)
    let var_ = cadr(args)
    row_begin(Str("<apply>")) |> ignore
    share_prmathml__t("<")
    tprinc(sym_) |> ignore
    share_prmathml__t(">")
    share_prmathml__t("<bvar>")
    ctmathml(var_) |> ignore
    share_prmathml__t("</bvar>")
    ctmathml(exp_) |> ignore
    row_end(Str("</apply>"))
  }
}

///|
fn lamd(vars : Value, def : Value) -> Value raise {
  row_begin(Str("<lambda>")) |> ignore
  let mut l = vars
  while l.truthy() {
    share_prmathml__t("<bvar>")
    ctmathml(car(l)) |> ignore
    share_prmathml__t("</bvar>")
    l = cdr(l)
  }
  ctmathml(def) |> ignore
  row_end(Str("</lambda>"))
}

///|
fn def_fun(_op : Value, args : Value) -> Value raise {
  let fn_ = car(args)
  let def = cadr(args)
  row_begin(Str("<declare type=\"fn\">")) |> ignore
  ctmathml(caar(fn_)) |> ignore
  lamd(cdr(fn_), def) |> ignore
  row_end(Str("</declare>"))
}

///|
fn init_share_n_cc_t_cm_ath_cm__cl_() -> Unit raise {
  let s = (x : String) => Value::Str(x)
  let fns : Array[(String, String)] = [
    ("sin", "sin/"),
    ("cos", "cos/"),
    ("tan", "tan/"),
    ("cot", "cot/"),
    ("sec", "sec/"),
    ("csc", "csc/"),
    ("asin", "arcsin/"),
    ("acos", "arccos/"),
    ("atan", "arctan/"),
    ("acot", "acot/"),
    ("asec", "asec/"),
    ("acsc", "acsc/"),
    ("sinh", "sinh/"),
    ("cosh", "cosh/"),
    ("tanh", "tanh/"),
    ("coth", "coth/"),
    ("sech", "sec/"),
    ("csch", "csch/"),
    ("asinh", "asinh/"),
    ("acosh", "acosh/"),
    ("atanh", "atanh/"),
    ("acoth", "acoth/"),
    ("asech", "asec/"),
    ("acsch", "acsch/"),
    ("ln", "ln/"),
    ("log", "log/"),
  ]
  for e in fns {
    share_prmathml__setup(sym("%" + e.0), [(q_ctfun, s(e.1))])
  }
  for e in fns {
    share_prmathml__setup(sym("$" + e.0), [(q_ctfun, s(e.1))])
  }
  // containers
  share_prmathml__setup(q_mlist, [(q_ct_proc, q_ctlist)])
  share_prmathml__setup(q_d_set, [(q_ct_proc, q_ctset)])
  share_prmathml__setup(q_d_matrix, [(q_ct_proc, q_ctmatrix)])
  share_prmathml__setup(sym("$vector"), [(q_ct_proc, q_ctvector)])
  // Operators and functions
  let ops : Array[(Value, String)] = [
    (q_mand, "and/"),
    (q_mor, "or/"),
    (q_mnot, "not/"),
    (q_d_xor, "xor/"),
    (q_mplus, "plus/"),
    (q_d_plus, "plus/"),
    (q_mminus, "minus/"),
    (q_d_minus, "minus/"),
    (q_mdif, "minus/"),
    (q_d_remainder, "rem/"),
    (q_d_max, "max/"),
    (q_d_min, "min/"),
    (q_mfactorial, "factorial/"),
    (q_mabs, "abs/"),
  ]
  for e in ops {
    share_prmathml__setup(e.0, [(q_ctfun, s(e.1))])
  }
  share_prmathml__setup(q_p_abs, [(q_ct_proc, q_abs)])
  let ops2 : Array[(Value, String)] = [
    (q_d_conjugate, "conjugate/"),
    (q_mnctimes, "times type=\"noncommutative\"/"),
    (q_mtimes, "times/"),
    (q_mexpt, "power/"),
    (q_mquotient, "divide/"),
  ]
  for e in ops2 {
    share_prmathml__setup(e.0, [(q_ctfun, s(e.1))])
  }
  share_prmathml__setup(q_rat, [(q_ct_proc, q_rat)])
  share_prmathml__setup(q_d_sqrt, [(q_ctfun, s("root/"))])
  share_prmathml__setup(q_p_sqrt, [(q_ctfun, s("root/"))])
  share_prmathml__setup(q_mquote, [(q_ctfun, s("quote/"))])
  let rels : Array[(Value, String)] = [
    (q_mgreaterp, "gt/"),
    (q_mgeqp, "geq/"),
    (q_mequal, "eq/"),
    (q_mnotequal, "neq/"),
    (q_mleqp, "leq/"),
    (q_mlessp, "lt/"),
  ]
  for e in rels {
    share_prmathml__setup(e.0, [(q_ct_proc, q_relation), (q_ctfun, s(e.1))])
  }
  share_prmathml__setup(q_mdefine, [(q_ct_proc, q_def_fun)])
  let procs : Array[(Value, Value, String)] = [
    (q_p_sum, q_sumprod, "sum/"),
    (q_d_sum, q_sumprod, "sum/"),
    (q_d_product, q_sumprod, "product/"),
    (q_p_product, q_sumprod, "product/"),
    (q_d_integrate, q_ctintegrate, "int/"),
    (q_p_integrate, q_ctintegrate, "int/"),
    (q_d_diff, q_ctdiff, "diff/"),
    (q_p_derivative, q_ctdiff, "diff/"),
    (q_d_limit, q_ctlimit, "limit/"),
    (q_p_limit, q_ctlimit, "limit/"),
  ]
  for e in procs {
    share_prmathml__setup(e.0, [(q_ct_proc, e.1), (q_ctfun, s(e.2))])
  }
}
