// Port of share/trigonometry/trigrat.lisp (D. Lazard, 1988): trigrat, a
// canonical simplified quasilinear form of a trigonometrical expression.

///|
/// (defun $listofei (e) ...): e is a CRE; collect in $lexp the kernels
/// %e^(..%i..) of its varlist, rename them in a copy of the CRE ($d2%) to
/// the symbols $_<genvar> collected in $lg.
fn d_listofei(e : Value) -> Value raise {
  set(q_d_d2_pct, copy_tree(car(e))) |> ignore
  set(q_d_lg, Nil) |> ignore
  set(q_d_lexp, Nil) |> ignore
  let mut lvar = caddr(symval(q_d_d2_pct))
  let mut lg = cadddr(symval(q_d_d2_pct))
  while lvar is Cons(_) {
    let mut v = car(lvar)
    // Check that we have a factor of %i. This test includes cases like %i,
    // and %i*x/2, which we get for e.g. sin(1) and sin(x/2).
    if mexptp(v).truthy() &&
      equal(cadr(v), q_d__pcte) &&
      eq(
        q_d__pcti,
        cdr(
          partition(
            if atom(caddr(v)) {
              list2(list1(q_mtimes), caddr(v))
            } else {
              caddr(v)
            },
            q_d__pcti,
            Fix(1L),
          ),
        ),
      ) {
      set(q_d_lexp, cons(v, symval(q_d_lexp))) |> ignore
      v = symbolconc(list2(Str("$_"), car(lg)))
      set(q_d_lg, cons(v, symval(q_d_lg))) |> ignore
      rplaca(lvar, v) |> ignore
    }
    lvar = cdr(lvar)
    lg = cdr(lg)
  }
  set(q_d_lg, cons(list1(q_mlist), symval(q_d_lg))) |> ignore
  set(q_d_lexp, cons(list1(q_mlist), symval(q_d_lexp))) |> ignore
  set(q_d_d2_pct, cons(symval(q_d_d2_pct), cdr(e)))
}

///|
/// The #$...$ top-level forms (each read as (meval* '<expr>)).
fn init_share_trigrat() -> Unit raise {
  meval_star(
    maxima_lit(
      "trigrat_equationp (e%) := not atom (e%) and member (op (e%), [\"=\", \"#\", \"<\", \"<=\", \">=\", \">\"])$",
    ),
  )
  |> ignore
  meval_star(
    maxima_lit(
      (
        #|trigrat(exp):=
        #|    if matrixp (exp) or listp (exp) or setp (exp) or trigrat_equationp (exp)
        #|    then map (trigrat, exp)
        #|    else block([e%,n%,d%,lg,f%,lexp,ls,d2%,l2%,algebraic:true,gcd:subres, ratfac:false,ratexpand:true],
        #|		e%: rat(ratsimp(expand(exponentialize(exp)))),
        #|		n%:num(e%),d%:denom(e%),
        #|		listofei(d%),
        #|		l2%:map(lambda([u%,v%],u%^((hipow(d2%,v%)+lopow(d2%,v%))/2)),
        #|				lexp,lg),
        #|		f%:if length(lexp)=0 then 1
        #|		  else if length(lexp)=1 then part(l2%,1)
        #|		  else apply("*",l2%),
        #|  		n%:demoivre(ratexpand(n%/f%)),
        #|	        d%:demoivre(ratexpand(d%/f%)),
        #|		e%:ratsimp(n%/d%,%i),
        #|		e%)$
      ),
    ),
  )
  |> ignore
}
