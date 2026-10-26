///|
test "numbers" {
  let big = expt(int(2), int(100))
  inspect(big, content="1267650600228229401496703205376")
  inspect(num_div(int(6), int(4)), content="3/2")
  inspect(num_add(Fix(9223372036854775807L), int(1)), content="9223372036854775808")
  inspect(num_mul(Fix(4294967296L), Fix(4294967296L)), content="18446744073709551616")
  inspect(num_floor(int(-7), b=int(2)).0, content="-4")
  inspect(num_floor(int(-7), b=int(2)).1, content="1")
  inspect(num_truncate(int(-7), b=int(2)).0, content="-3")
  inspect(num_round(int(5), b=int(2)).0, content="2")
  inspect(num_round(int(7), b=int(2)).0, content="4")
  inspect(isqrt(expt(int(10), int(40))), content="100000000000000000000")
  inspect(ash(int(-5), -1), content="-3")
  inspect(integer_length(int(255)), content="8")
  inspect(to_double(make_ratio(1N, 3N)), content="0.3333333333333333")
  inspect(rational(Flo(0.5)), content="1/2")
  inspect(num_compare(Flo(0.1), make_ratio(1N, 10N)), content="1")
  inspect(lsqrt(Flo(-4.0)), content="#C(0.0 2.0)")
  inspect(num_gcd(int(12), int(18)), content="6")
}

///|
test "float printing" {
  let xs = [1.0, 0.1, 1.5e10, 1.0e7, 1234567.0, 1.0e-3, 1.0e-4, 123.456, 1.0e100, -0.0, 1.0 / 3.0]
  inspect(
    xs.map(float_to_string).join(" "),
    content="1.0 0.1 1.5e10 1.0e7 1234567.0 0.001 1.0e-4 123.456 1.0e100 -0.0 0.3333333333333333",
  )
}

///|
test "reader and printer" {
  let x = try! lread("((mplus simp) 1 $x |$Foo| |$BAR| \"s\" #\\a 1.5d0 2/4 (a . b))")
  inspect(
    x,
    content="((mplus simp) 1 $x |$Foo| $bar \"s\" #\\a 1.5 1/2 (a . b))",
  )
  inspect(prin1_to_string(sym("$BAR")), content="|$BAR|")
}

///|
test "format" {
  inspect(try! format_to_string("~a + ~s = ~d~%", [sym("x"), Str("y"), int(3)]), content="x + \"y\" = 3\n")
  inspect(try! format_to_string("~{~a~^, ~}", [list([int(1), int(2), int(3)])]), content="1, 2, 3")
  inspect(try! format_to_string("~:[no~;yes~]", [t]), content="yes")
  inspect(try! format_to_string("~5,2f|~,3f", [Flo(3.14159), Flo(2.0)]), content=" 3.14|2.000")
  inspect(try! format_to_string("~r ~:r ~@r", [int(42), int(3), int(14)]), content="forty-two third XIV")
}

///|
test "hash and lists" {
  let h = make_hash_table(kind=Equal)
  try! sethash(list([int(1), int(2)]), h, sym("a")) |> ignore
  inspect(try! gethash(list([int(1), int(2)]), h), content="a")
  inspect(sort_list(list([int(3), int(1), int(2)]), (a, b) => num_lt(a, b)), content="(1 2 3)")
  inspect(nreverse(list([int(1), int(2), int(3)])), content="(3 2 1)")
  inspect(append(list([int(1)]), list([int(2)])), content="(1 2)")
}
