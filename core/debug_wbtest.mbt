///|
test "debug opers list" {
  initialize()
  let l = symval(q_n_staropers_list)
  println("len=\{length(l)}")
  let mut p = l
  let mut i = 0
  while p is Cons(c) && i < 40 {
    println(prin1_to_string(car(c.car)))
    p = c.cdr
    i += 1
  }
}
