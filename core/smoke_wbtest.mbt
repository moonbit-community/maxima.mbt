///|
fn smoke__s(s : String) -> Value raise {
  simplifya(maxima_lit(s), Nil)
}

///|
test "smoke: init and simplify" {
  initialize()
  let e = lread("((mplus) 1 2 $x $x ((mtimes) 3 $y) ((mexpt) $x 2))")
  inspect(simplifya(e, Nil), content="((mplus simp) 3 ((mtimes simp) 2 $x) ((mexpt simp) $x 2) ((mtimes simp) 3 $y))")
}

