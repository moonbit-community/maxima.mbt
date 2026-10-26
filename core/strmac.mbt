// Port of src/strmac.lisp: data representation macros (as functions).
// Macros taking `&rest args` receive the Lisp list of their arguments.

///|
fn g_rep_operator(exp_ : Value) -> Value raise {
  caar(exp_)
}

///|
fn g_rep_operands(exp_ : Value) -> Value raise {
  cdr(exp_)
}

///|
fn g_rep_first_operand(exp_ : Value) -> Value raise {
  cadr(exp_)
}

///|
fn make_mplus(args : Value) -> Value raise {
  cons(list1(q_mplus), args)
}

///|
fn make_mplus_l(llist : Value) -> Value raise {
  cons(list1(q_mplus), llist)
}

///|
fn make_mplus_simp(args : Value) -> Value raise {
  cons(list2(q_mplus, q_simp), args)
}

///|
fn make_mtimes(args : Value) -> Value raise {
  cons(list1(q_mtimes), args)
}

///|
fn make_mtimes_l(llist : Value) -> Value raise {
  cons(list1(q_mtimes), llist)
}

///|
fn make_mtimes_simp(args : Value) -> Value raise {
  cons(list2(q_mtimes, q_simp), args)
}

///|
fn make_mexpt(thing_being_raised_to_power : Value, expt_ : Value) -> Value raise {
  list3(list1(q_mexpt), thing_being_raised_to_power, expt_)
}

///|
fn make_mexpt_l(llist : Value) -> Value raise {
  cons(list1(q_mexpt), llist)
}

///|
fn make_mexpt_simp(
  thing_being_raised_to_power : Value,
  expt_ : Value,
) -> Value raise {
  list3(list2(q_mexpt, q_simp), thing_being_raised_to_power, expt_)
}

///|
fn mexpt_base(mexpt : Value) -> Value raise {
  cadr(mexpt)
}

///|
fn mexpt_expt(mexpt : Value) -> Value raise {
  caddr(mexpt)
}

///|
fn make_mequal(lhs : Value, rhs : Value) -> Value raise {
  list3(list1(q_mequal), lhs, rhs)
}

///|
fn make_mequal_l(llist : Value) -> Value raise {
  cons(list1(q_mequal), llist)
}

///|
fn make_mequal_simp(lhs : Value, rhs : Value) -> Value raise {
  list3(list2(q_mequal, q_simp), lhs, rhs)
}

///|
fn mequal_lhs(mequal : Value) -> Value raise {
  cadr(mequal)
}

///|
fn mequal_rhs(mequal : Value) -> Value raise {
  caddr(mequal)
}

///|
fn make_mlist(args : Value) -> Value raise {
  cons(list1(q_mlist), args)
}

///|
fn make_mlist_l(llist : Value) -> Value raise {
  cons(list1(q_mlist), llist)
}

///|
fn make_mlist_simp(args : Value) -> Value raise {
  cons(list2(q_mlist, q_simp), args)
}

///|
fn make_mtext(args : Value) -> Value raise {
  cons(list1(q_mtext), args)
}

///|
fn make_rat(args : Value) -> Value raise {
  cons(list1(q_rat), args)
}

///|
fn make_rat_simp(args : Value) -> Value raise {
  cons(list2(q_rat, q_simp), args)
}

///|
fn make_rat_body(numer : Value, denom : Value) -> Value raise {
  cons(numer, denom)
}

///|
fn rat_numer(rat : Value) -> Value raise {
  cadr(rat)
}

///|
fn rat_denom(rat : Value) -> Value raise {
  caddr(rat)
}

// Schematic of MRAT form:
//  ((MRAT SIMP <varlist> <genvars>) <numer> . <denom>)
// Schematic of <numer> and <denom>:
//  (<genvar> <exponent 1> <coefficient 1> ...)
// Representation for X^2+1:
//  ((MRAT SIMP ($X) (G0001)) (G0001 2 1 0 1) . 1)

///|
fn mrat_body(mrat : Value) -> Value raise {
  cdr(mrat)
}

///|
fn mrat_numer(mrat : Value) -> Value raise {
  cadr(mrat)
}

///|
fn mrat_denom(mrat : Value) -> Value raise {
  cddr(mrat)
}

///|
/// `((mrat ,varlist ,genvars) ,numer . ,denom)`
fn make_mrat(
  varlist : Value,
  genvars : Value,
  numer : Value,
  denom : Value,
) -> Value raise {
  cons(list3(q_mrat, varlist, genvars), cons(numer, denom))
}

///|
fn make_mrat_body(numer : Value, denom : Value) -> Value raise {
  cons(numer, denom)
}

///|
fn trig_cannon(operator : Value) -> Value raise {
  get(operator, q_trig_cannon)
}

///|
/// Linear equation -- cons of linear term and constant term.
fn make_lineq(linear : Value, constant : Value) -> Value raise {
  cons(linear, constant)
}

///|
fn lineq_linear(lineq : Value) -> Value raise {
  car(lineq)
}

///|
fn lineq_constant(lineq : Value) -> Value raise {
  cdr(lineq)
}

///|
/// Solutions -- a pair of polynomial/multiplicity lists
fn make_solution(wins : Value, losses : Value) -> Value raise {
  cons(wins, losses)
}

///|
fn solution_wins(solution : Value) -> Value raise {
  car(solution)
}

///|
fn solution_losses(solution : Value) -> Value raise {
  cdr(solution)
}

///|
/// Polynomials -- these appear in the numerator or denominator of MRAT
/// forms.
fn make_mrat_poly(var_ : Value, terms : Value) -> Value raise {
  cons(var_, terms)
}

///|
fn poly_var(poly : Value) -> Value raise {
  car(poly)
}

///|
fn poly_terms(poly : Value) -> Value raise {
  cdr(poly)
}
