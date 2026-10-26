// Port of src/mhayat.lisp: macros and data-structure accessors for the
// HAYAT finite power series package (taylor).
//
// Power series have the following format when seen outside the power
// series package:
//
//    ((MRAT SIMP <varlist> <genvar> <tlist> trunc) <poly-form>)
//
// The <poly-forms> consist of a header and list of exponent-coefficient
// pairs:
//
//   (PS (<var> . <ord-num>) (<trunc-lvl>)
//	  (<exponent> . <coeff>) (<exponent> . <coeff>) . . .)
//
// The <var> component is a gensym which represents the kernel of the power
// series; <ord-num> is a relative ordering for the kernels in a multivariate
// expansion; <trunc-lvl> is the highest degree retained. Terms are ordered by
// increasing degree.
//
// Function-like macros are translated as functions. Macros whose arguments
// are evaluated lazily (LET-PW, TLIST-MAPC, MLET) are expanded inline at
// their call sites; the functions below only approximate them.

///|
fn pszero(var_ : Value, pw : Value) -> Value raise {
  ignore(var_)
  ignore(pw)
  cons(Fix(0L), Fix(1L))
}

///|
fn psp(e : Value) -> Value raise {
  lbool(eq(car(e), q_ps))
}

///|
fn pscoefp(e : Value) -> Value raise {
  lbool(!eq(car(e), q_ps))
}

///|
fn psquo(ps1 : Value, ps2? : Value = Nil) -> Value raise {
  if ps2 is Nil {
    psexpt(ps1, rcmone())
  } else {
    pstimes(ps1, psexpt(ps2, rcmone()))
  }
}

///|
fn pslog_gvar(gvar : Value) -> Value raise {
  pslog2(get_inverse(gvar))
}

///|
fn gvar_o(e : Value) -> Value raise {
  cadr(e)
}

///|
fn gvar(e : Value) -> Value raise {
  car(cadr(e))
}

///|
fn eqgvar(x : Value, y : Value) -> Value raise {
  lbool(eq(car(x), car(y)))
}

///|
fn pointerp(x : Value, y : Value) -> Value raise {
  lbool(num_gt(cdr(x), cdr(y)))
}

///|
fn poly_data(p : Value) -> Value raise {
  caddr(p)
}

///|
fn trunc_lvl(p : Value) -> Value raise {
  car(caddr(p))
}

///|
fn terms(p : Value) -> Value raise {
  cdddr(p)
}

///|
fn lt(terms : Value) -> Value raise {
  car(terms)
}

///|
fn le(terms : Value) -> Value raise {
  caar(terms)
}

///|
fn lc(terms : Value) -> Value raise {
  cdar(terms)
}

///|
fn e(term : Value) -> Value raise {
  car(term)
}

///|
fn c(term : Value) -> Value raise {
  cdr(term)
}

///|
fn n__term(terms : Value) -> Value raise {
  cdr(terms)
}

///|
fn mono_term_q(terms : Value) -> Value raise {
  lbool(cdr(terms) is Nil)
}

///|
fn nconc_terms(oldterms : Value, newterms : Value) -> Value raise {
  nconc(oldterms, newterms)
}

///|
fn term(e : Value, c : Value) -> Value raise {
  cons(e, c)
}

///|
fn make_ps(
  var_or_data_poly : Value,
  pdata_or_terms : Value,
  terms? : Value,
) -> Value raise {
  match terms {
    Some(ts) => cons(q_ps, cons(var_or_data_poly, cons(pdata_or_terms, ts)))
    None =>
      cons(
        q_ps,
        cons(
          cadr(var_or_data_poly),
          cons(caddr(var_or_data_poly), pdata_or_terms),
        ),
      )
  }
}

///|
/// Be sure that PS has more than one term when deleting the first.
fn del_lt(ps : Value) -> Value raise {
  rplacd(cddr(ps), cddddr(ps))
}

///|
fn add_term(terms : Value, term_or_e? : Value, c? : Value) -> Value raise {
  match (term_or_e, c) {
    (None, _) => rplacd(terms, Nil)
    (Some(t1), None) => rplacd(terms, cons(t1, cdr(terms)))
    (Some(e1), Some(c1)) => rplacd(terms, cons(cons(e1, c1), cdr(terms)))
  }
}

///|
/// `(add-term-&-pop terms . args)`: adds the term and returns the new value
/// of TERMS (the caller must assign it, since the macro does a SETQ).
fn add_term__amp_pop(terms : Value, args : Value) -> Value raise {
  match length(args) {
    0 => add_term(terms) |> ignore
    1 => add_term(terms, term_or_e=car(args)) |> ignore
    _ => add_term(terms, term_or_e=car(args), c=cadr(args)) |> ignore
  }
  cdr(terms)
}

///|
fn change_coef(terms : Value, coef : Value) -> Value raise {
  rplacd(car(terms), coef)
}

///|
fn change_lc(terms : Value, coef : Value) -> Value raise {
  rplacd(car(terms), coef)
}

///|
fn getdisrep(var_ : Value) -> Value raise {
  get(car(var_), q_disrep)
}

///|
fn getdiff(var_ : Value) -> Value raise {
  get(car(var_), q_diff)
}

///|
fn lt_poly(p : Value) -> Value raise {
  make_ps(gvar_o(p), poly_data(p), terms=list1(lt(terms(p))))
}

///|
fn oper_name(func : Value) -> Value raise {
  if atom(func) {
    func
  } else {
    caar(func)
  }
}

///|
fn oper_namep(oper_form : Value) -> Value raise {
  lbool(atom(oper_form))
}

///|
fn integer_subscriptp(subscr_fun : Value) -> Value raise {
  lbool(every(x => integerp(x), cdr(subscr_fun)))
}

///|
/// `(mlet varl vals comp)` = `(mbinding (varl vals) comp)`. The body COMP
/// is a form evaluated inside the binding; here it is given as a Maxima
/// expression and evaluated with MEVAL.
fn mlet(varl : Value, vals : Value, comp : Value) -> Value raise {
  mbinding(list2(varl, vals), list1(comp))
}

// Accessors for the MRAT header
//    ((MRAT SIMP <varlist> <genvar> <tlist> trunc) <poly-form>)

///|
fn mrat_header(mrat : Value) -> Value raise {
  car(mrat)
}

///|
fn mrat_varlist(mrat : Value) -> Value raise {
  third(car(mrat))
}

///|
fn mrat_genvar(mrat : Value) -> Value raise {
  fourth(car(mrat))
}

///|
fn mrat_tlist(mrat : Value) -> Value raise {
  fifth(car(mrat))
}

///|
fn mrat_ps(mrat : Value) -> Value raise {
  cdr(mrat)
}

// TLIST is a list of datums, each of the form
//	(<var> <trunc-lvl stack> <pt of expansion>
//	       <list of switches> <internal var = gvar> . <ord-num>)
// Possible switches: $asymp, multi, multivar.

///|
fn datum_var(datum : Value) -> Value raise {
  car(datum)
}

///|
fn trunc_stack(datum : Value) -> Value raise {
  cadr(datum)
}

///|
fn current_trunc(datum : Value) -> Value raise {
  car(cadr(datum))
}

///|
fn orig_trunc(datum : Value) -> Value raise {
  car(last(cadr(datum)))
}

///|
fn exp_pt(datum : Value) -> Value raise {
  caddr(datum)
}

///|
fn switches(datum : Value) -> Value raise {
  cadddr(datum)
}

///|
fn switch(sw : Value, datum : Value) -> Value raise {
  cdr(assq(sw, cadddr(datum)))
}

///|
fn int_var(datum : Value) -> Value raise {
  cddddr(datum)
}

///|
fn data_gvar_o(data : Value) -> Value raise {
  cddddr(data)
}

///|
fn int_gvar(datum : Value) -> Value raise {
  car(cddddr(datum))
}

///|
fn data_gvar(data : Value) -> Value raise {
  car(cddddr(data))
}

///|
fn get_inverse(gensym_ : Value) -> Value raise {
  cdr(assq(gensym_, symval(q_ivars)))
}

///|
fn get_key_var(gensym_ : Value) -> Value raise {
  cdr(assq(gensym_, symval(q_key_vars)))
}

///|
fn gvar__gtvar(gvar : Value) -> Value raise {
  cdr(assq(gvar, symval(q_key_vars)))
}

///|
fn dummy_var() -> Value raise {
  cdar(symval(q_key_vars))
}

///|
fn first_datum() -> Value raise {
  car(symval(q_tlist))
}

///|
fn get_datum(expr : Value, not_canonicalized_q? : Value = Nil) -> Value raise {
  if not_canonicalized_q.truthy() {
    assol(expr, symval(q_tlist))
  } else {
    assoc_equal(expr, symval(q_tlist))
  }
}

///|
fn var_data(var_ : Value) -> Value raise {
  assoc_equal(var_, symval(q_tlist))
}

///|
fn gvar_data(gvar : Value) -> Value raise {
  var_data(gvar__gtvar(gvar))
}

///|
fn ps_data(ps : Value) -> Value raise {
  gvar_data(gvar(ps))
}

///|
fn t_o_var(gensym_ : Value) -> Value raise {
  current_trunc(get_datum(get_key_var(gensym_)))
}

///|
fn gvar_trunc(gvar : Value) -> Value raise {
  current_trunc(gvar_data(gvar))
}

///|
fn ps_arg_trunc(ps : Value) -> Value raise {
  gvar_trunc(gvar(ps))
}

///|
fn ps_le(ps : Value) -> Value raise {
  caar(cdddr(ps))
}

///|
fn ps_le_star(ps : Value) -> Value raise {
  if psp(ps).truthy() {
    ps_le(ps)
  } else {
    cons(Fix(0L), Fix(1L))
  }
}

///|
fn ps_lc(ps : Value) -> Value raise {
  cdar(cdddr(ps))
}

///|
fn ps_lc_star(ps : Value) -> Value raise {
  if psp(ps).truthy() {
    ps_lc(ps)
  } else {
    ps
  }
}

///|
fn ps_lt(ps : Value) -> Value raise {
  car(cdddr(ps))
}

///|
/// GETEXP-LT is not defined anywhere in Maxima; calling it is an error.
fn getexp_le(fun : Value) -> Value raise {
  ignore(fun)
  raise LispError::SimpleError("The function GETEXP-LT is undefined.")
}

///|
fn getexp_lc(fun : Value) -> Value raise {
  ignore(fun)
  raise LispError::SimpleError("The function GETEXP-LT is undefined.")
}

///|
/// `(let-pw datum pw comp)`: COMP must be computed while the truncation
/// PW is pushed on DATUM, so call sites use `mhayat__let_pw` with a closure.
/// This eager version can only return the already computed COMP.
fn let_pw(datum : Value, pw : Value, comp : Value) -> Value raise {
  push_pw(datum, pw) |> ignore
  pop_pw(datum) |> ignore
  comp
}

///|
/// The real expansion of LET-PW: push PW on DATUM, run COMP, pop.
fn mhayat__let_pw(datum : Value, pw : Value, comp : () -> Value raise) -> Value raise {
  let d = datum
  push_pw(d, pw) |> ignore
  let r = comp()
  pop_pw(d) |> ignore
  r
}

///|
/// `(tlist-mapc datum-var . comp)`: COMP is given as a function of the
/// datum here.
fn tlist_mapc(datum_var : Value, comp : Value) -> Value raise {
  ignore(datum_var)
  mapc(d => funcall(comp, [d]) |> ignore, symval(q_tlist))
}

///|
/// Run F on every datum of TLIST (the real expansion of TLIST-MAPC).
fn mhayat__tlist_mapc(f : (Value) -> Unit raise) -> Value raise {
  mapc(f, symval(q_tlist))
}

///|
fn find_lexp(
  exp_ : Value,
  e_start? : Value = Nil,
  errflag? : Value = Nil,
  accum_vars? : Value = Nil,
) -> Value raise {
  ignore(accum_vars)
  get_lexp(exp_, e_start, errflag)
}

///|
fn tay_err(msg : Value) -> Value raise {
  throw_tag(q_tay_err, list2(msg, symval(q_last_exp)))
}

///|
fn zero_warn(exp_ : Value) -> Value raise {
  mtell(
    list([
      Str("taylor: assumed to be zero: ~M~%"),
      list3(list1(q_mlabel), Nil, exp_),
    ]),
  )
}

// Macros for manipulating expansion data in the expansion table.

///|
fn exp_datum_lt(fun : Value, exp_datum : Value) -> Value raise {
  if atom(cadr(exp_datum)) {
    funcall(cadr(exp_datum), [cdr(fun)])
  } else {
    copy_tree(cadr(exp_datum))
  }
}

///|
fn exp_datum_le(fun : Value, exp_datum : Value) -> Value raise {
  car(exp_datum_lt(fun, exp_datum))
}

///|
fn exp_fun(exp_datum : Value) -> Value raise {
  if atom(car(exp_datum)) {
    car(exp_datum)
  } else {
    caar(exp_datum)
  }
}

// Access to the extendable portions of a polynomial.

///|
fn ext_fun(p : Value) -> Value raise {
  cadr(poly_data(p))
}

///|
fn ext_args(p : Value) -> Value raise {
  caddr(poly_data(p))
}

///|
fn extendablep(p : Value) -> Value raise {
  let d = poly_data(p)
  if car(d) is Nil {
    t
  } else {
    cdr(d)
  }
}

///|
fn exactp(p : Value) -> Value raise {
  lbool(trunc_lvl(p) is Nil)
}

///|
fn nexactp(p : Value) -> Value raise {
  trunc_lvl(p)
}

///|
fn get_ps_form(fun : Value) -> Value raise {
  get(fun, q_sp2)
}

///|
fn term_disrep(term : Value, p : Value) -> Value raise {
  mul2_star(
    srdis(cdr(term)),
    power_star(get_inverse(gvar(p)), edisrep(car(term))),
  )
}

// Coefficient arithmetic

///|
fn rczero() -> Value raise {
  cons(Fix(0L), Fix(1L))
}

///|
fn rcone() -> Value raise {
  cons(Fix(1L), Fix(1L))
}

///|
fn rcfone() -> Value raise {
  cons(Flo(1.0), Flo(1.0))
}

///|
fn rctwo() -> Value raise {
  cons(Fix(2L), Fix(1L))
}

///|
fn rcmone() -> Value raise {
  cons(Fix(-1L), Fix(1L))
}

///|
fn rczerop(r : Value) -> Value raise {
  let x = car(r)
  lbool(numberp(x) && zerop(x))
}

///|
fn rcintegerp(c : Value) -> Value raise {
  lbool(integerp(car(c)) && equal(cdr(c), Fix(1L)))
}

///|
fn rcpintegerp(c : Value) -> Value raise {
  lbool(rcintegerp(c).truthy() && plusp(car(c)))
}

///|
fn rcmintegerp(c : Value) -> Value raise {
  lbool(rcintegerp(c).truthy() && minusp(car(c)))
}

///|
fn rcplus(x : Value, y : Value) -> Value raise {
  ratplus(x, y)
}

///|
fn rcdiff(x : Value, y : Value) -> Value raise {
  ratdif(x, y)
}

///|
fn rcminus(x : Value) -> Value raise {
  ratminus(x)
}

///|
fn rctimes(x : Value, y : Value) -> Value raise {
  rattimes(x, y, t)
}

///|
fn rcquo(x : Value, y : Value) -> Value raise {
  ratquotient(x, y)
}

///|
fn rcdisrep(x : Value) -> Value raise {
  cdisrep(x)
}

///|
fn rcderiv(x : Value, v : Value) -> Value raise {
  ratderivative(x, v)
}

///|
fn rcderivx(x : Value) -> Value raise {
  ratdx1(car(x), cdr(x))
}

// Exponent arithmetic (also used in pade.lisp and nalgfa.lisp).
// An exponent is (n . d); an infinite exponent is nil.

///|
fn infp(x : Value) -> Value raise {
  lbool(x is Nil)
}

///|
fn inf() -> Value raise {
  Nil
}

///|
fn e_(e1 : Value, e2? : Value) -> Value raise {
  match e2 {
    Some(e2) => ediff(e1, e2)
    None => cons(num_neg(car(e1)), cdr(e1))
  }
}

///|
fn e_sl_sl(e1 : Value, e2? : Value) -> Value raise {
  match e2 {
    Some(e2) => equo(e1, e2)
    None => erecip(e1)
  }
}

///|
fn e_gt_eq(e1 : Value, e2 : Value) -> Value raise {
  let r = e_gt(e1, e2)
  if r.truthy() {
    r
  } else {
    e_eq(e1, e2)
  }
}

///|
fn ezero() -> Value raise {
  cons(Fix(0L), Fix(1L))
}

///|
fn eone() -> Value raise {
  cons(Fix(1L), Fix(1L))
}

///|
fn rcinv(r : Value) -> Value raise {
  ratinvert(r)
}
