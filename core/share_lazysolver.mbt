// Port of share/contrib/diffequations/lazysolver.lisp (Barton Willis,
// 2004): checked solutions of algebraic systems (checkedalgsys, aalgsys),
// for odelin. The algorithms are shared with the port of odelin.lisp
// (core/share_odelin.mbt).

///|
fn variablep(e : Value) -> Value raise {
  lbool(share_odelin__variablep(e))
}

///|
/// Check that sol is a solution to eqs and that nz is nonvanishing.
fn d_checksolution(sol : Value, eqs : Value, nz? : Value) -> Value raise {
  share_odelin__checksolution(sol, eqs, match nz {
    Some(v) => v
    None => list1(list1(q_mlist))
  })
}

///|
/// The function 'checkedalgsys' tries to return the "simplest" solution. It
/// uses this simple-minded measure of simple.
fn my_expr_size(e : Value) -> Value raise {
  int(share_odelin__my_expr_size(e))
}

///|
fn xmy_expr_size(e : Value) -> Value raise {
  int(share_odelin__xmy_expr_size(e))
}

///|
fn my_freeof(unks : Value, q : Value) -> Value raise {
  lbool(share_odelin__my_freeof(unks, q))
}

///|
/// Solve 'eqs' for 'vars' and return a solution such that no expression in
/// the Maxima list 'nz' vanishes. Since 'algsys' sometimes returns bogus
/// solutions, checkedalgsys checks the putative solutions and rejects bogus
/// solutions. To return the 'simplest' solution, the putative solutions are
/// sorted using 'my-expr-size.
fn d_checkedalgsys(eqs : Value, vars : Value, nz? : Value) -> Value raise {
  share_odelin__checkedalgsys(eqs, vars, match nz {
    Some(v) => v
    None => list1(list1(q_mlist))
  })
}

///|
fn nonconstant_factors(e : Value, vars : Value) -> Value raise {
  share_odelin__nonconstant_factors(e, vars)
}

///|
fn unks_in_eq(eq_ : Value, unks : Value) -> Value raise {
  share_odelin__unks_in_eq(eq_, unks)
}

///|
fn d_aalgsys(e_eqs : Value, eqs : Value, unks : Value, nz? : Value) -> Value raise {
  share_odelin__aalgsys(e_eqs, eqs, unks, match nz {
    Some(v) => v
    None => list1(list1(q_mlist))
  })
}

///|
fn init_share_lazysolver() -> Unit raise {
  d_put(sym("$lazysolver"), int(1), q_d_version) |> ignore
  d_load(Str("odeutils")) |> ignore
}
