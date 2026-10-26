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

///|
test "nil reads as Nil" {
  inspect(try! lread("(a nil ())"), content="(a nil nil)")
  assert_true(try! lread("nil") is Nil)
}

///|
test "sbcl set order" {
  let l = (xs : Array[Int]) => list(xs.map(int))
  inspect(try! union_(l([1, 2, 3]), l([3, 4, 5])), content="(5 4 1 2 3)")
  inspect(try! union_(l([1, 2, 3, 4, 5, 6]), l([9, 1])), content="(6 5 4 3 2 9 1)")
  inspect(try! intersection(l([4, 3, 2]), l([1, 2, 3, 4, 5])), content="(2 3 4)")
  inspect(try! intersection(l([1, 2, 3]), l([3, 2, 1])), content="(3 2 1)")
  inspect(try! set_difference(l([1, 2, 3, 4, 5]), l([2, 9])), content="(5 4 3 1)")
}

///|
test "complex arithmetic like sbcl" {
  let c1 = Value::Cplx(Flo(1.0), Value::Flo(2.0))
  let c2 = Value::Cplx(Flo(3.0), Value::Flo(-7.0))
  inspect(try! num_div(c1, c2), content="#C(-0.18965517241379312 0.2241379310344828)")
  inspect(try! num_div(Value::Flo(2.0), c2), content="#C(0.10344827586206898 0.24137931034482762)")
  inspect(try! num_add(Value::Cplx(Flo(1.0), Value::Flo(-0.0)), Value::Flo(2.0)), content="#C(3.0 0.0)")
  inspect(try! num_mul(Value::Cplx(Flo(1.0), Value::Flo(-0.0)), Value::Flo(2.0)), content="#C(2.0 -0.0)")
  inspect(try! num_add(Value::Flo(2.0), Value::Cplx(Flo(1.0), Value::Flo(-0.0))), content="#C(3.0 0.0)")
  inspect(try! num_sub(Value::Cplx(Flo(1.0), Value::Flo(-0.0)), Value::Flo(2.0)), content="#C(-1.0 -0.0)")
  inspect(try! num_sub(Value::Flo(2.0), Value::Cplx(Flo(1.0), Value::Flo(0.0))), content="#C(1.0 0.0)")
}

///|
test "float traps" {
  let big = Value::Flo(1.0e308)
  let r = try num_mul(big, big) catch { e => Value::Str("\{e}") } noraise { v => v }
  inspect(r, content="\"floating-point-overflow: arithmetic error FLOATING-POINT-OVERFLOW signalled\"")
}

///|
test "libm and complex sqrt like sbcl" {
  inspect(try! lsqrt(Value::Cplx(Value::Flo(3.0), Value::Flo(1.0))), content="#C(1.755317301824428 0.28484878459314106)")
  inspect(try! lsqrt(Value::Flo(-4.0)), content="#C(0.0 2.0)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(2.886751345948129e-301 -1.7320508075688772)")
  inspect(try! lexp(Value::Flo(1.6)), content="4.953032424395115")
  inspect(try! llog(Value::Flo(1.6)), content="0.47000362924573563")
  inspect(try! expt(Value::Flo(2.5), Value::Flo(1.3)), content="3.2909555108355937")
}

///|
test "complex elementary functions like sbcl" {
  inspect(try! llog(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(-0.6931471805599453 0.9272952180016123)")
  inspect(try! llog(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(0.8047189562170501 0.4636476090008061)")
  inspect(try! llog(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(1.0986122886681098 -3.141592653589793)")
  inspect(try! llog(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(0.5596157879354227 0.0)")
  inspect(try! llog(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(0.6931471805599453 3.141592653589793)")
  inspect(try! llog(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(0.6931471805599453 -3.141592653589793)")
  inspect(try! llog(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(0.7234594914681627 -1.3258176636680326)")
  inspect(try! llog(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(0.34657359027997264 0.7853981633974483)")
  inspect(try! llog(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(-391.0928922187078 0.7853981633974483)")
  inspect(try! llog(Value::Cplx(Value::Flo(1.0e200), Value::Flo(1.0e200))), content="#C(460.8635921890891 0.7853981633974483)")
  inspect(try! llog(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(0.11157177565710488 0.4636476090008061)")
  inspect(try! llog(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(1.1865217783213036 1.7861540264926346)")
  inspect(try! llog(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(0.6931471805599453 1.5707963267948966)")
  inspect(try! llog(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(0.6931471805599453 -1.5707963267948966)")
  inspect(try! llog(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(0.18232155679395462 -3.141592653589793)")
  inspect(try! llog(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(5.991492671316996 0.007499859379745903)")
  inspect(try! llog(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(-0.05013609442205354 -1.5707963267948966)")
  inspect(try! llog(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(1.084519607175155 1.0003621183627505)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(0.6324555320336759 0.31622776601683794)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(1.455346690225355 0.34356074972251244)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(2.886751345948129e-301 -1.7320508075688772)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(1.3228756555322954 0.0)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(0.0 1.4142135623730951)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(0.0 -1.4142135623730951)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(1.1317139242778693 -0.8836155308755134)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(1.09868411346781 0.45508986056222733)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(1.09868411346781e-85 4.550898605622273e-86)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(1.0e200), Value::Flo(1.0e200))), content="#C(1.09868411346781e100 4.550898605622274e99)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(1.0290855136357462 0.24293413587832283)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(1.1348277117765146 1.4099056476998453)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(1.0 1.0)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(1.0 -1.0)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(0.0 -1.0954451150103321)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(20.00014062252815 0.07499947266922717)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(0.6896013255101587 -0.6896013255101586)")
  inspect(try! lsqrt(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(1.5091953511727105 0.8248320183617555)")
  inspect(try! lasin(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(0.28062956229180586 0.4051123371780309)")
  inspect(try! lasin(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(1.0634400235777521 1.4693517443681852)")
  inspect(try! lasin(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(-1.5707963267948966 -1.762747174039086)")
  inspect(try! lasin(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(1.5707963267948966 -1.158810360429947)")
  inspect(try! lasin(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(-1.5707963267948966 1.3169578969248166)")
  inspect(try! lasin(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(-1.5707963267948966 1.3169578969248166)")
  inspect(try! lasin(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(0.22101863562288385 -1.4657153519472905)")
  inspect(try! lasin(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(0.6662394324925153 1.0612750619050357)")
  inspect(try! lasin(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(1.0e-170 1.0e-170)")
  inspect(try! lasin(Value::Cplx(Value::Flo(1.0e200), Value::Flo(1.0e200))), content="#C(0.7853981633974483 461.55673936964905)")
  inspect(try! lasin(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(0.8959074812088902 0.7328576759736453)")
  inspect(try! lasin(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(-0.20620954109246065 1.9003216649977321)")
  inspect(try! lasin(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(0.0 1.4436354751788103)")
  inspect(try! lasin(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(0.0 -1.4436354751788103)")
  inspect(try! lasin(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(-1.5707963267948966 0.6223625037147786)")
  inspect(try! lasin(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(1.5632964439801773 6.684638289636928)")
  inspect(try! lasin(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(0.0 -0.8463699602485695)")
  inspect(try! lasin(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(0.5454064822477562 1.7903012744337676)")
  inspect(try! lacos(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(1.2901667645030908 -0.4051123371780309)")
  inspect(try! lacos(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(0.5073563032171445 -1.4693517443681852)")
  inspect(try! lacos(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(3.141592653589793 1.762747174039086)")
  inspect(try! lacos(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(0.0 1.158810360429947)")
  inspect(try! lacos(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(3.141592653589793 -1.3169578969248166)")
  inspect(try! lacos(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(3.141592653589793 -1.3169578969248166)")
  inspect(try! lacos(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(1.3497776911720127 1.4657153519472905)")
  inspect(try! lacos(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(0.9045568943023813 -1.0612750619050357)")
  inspect(try! lacos(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(1.5707963267948966 -1.0e-170)")
  inspect(try! lacos(Value::Cplx(Value::Flo(1.0e200), Value::Flo(1.0e200))), content="#C(0.7853981633974484 -461.55673936964905)")
  inspect(try! lacos(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(0.6748888455860064 -0.7328576759736453)")
  inspect(try! lacos(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(1.7770058678873573 -1.9003216649977321)")
  inspect(try! lacos(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(1.5707963267948966 -1.4436354751788103)")
  inspect(try! lacos(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(1.5707963267948966 1.4436354751788103)")
  inspect(try! lacos(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(3.141592653589793 -0.6223625037147786)")
  inspect(try! lacos(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(0.007499882814719241 -6.684638289636928)")
  inspect(try! lacos(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(1.5707963267948966 0.8463699602485695)")
  inspect(try! lacos(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(1.0253898445471405 -1.7903012744337676)")
  inspect(try! latan(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(0.3373704711117763 0.37908687234202215)")
  inspect(try! latan(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(1.1780972450961724 0.1732867951399863)")
  inspect(try! latan(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(-1.2490457723982544 -1.0e-301)")
  inspect(try! latan(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(1.0516502125483738 0.0)")
  inspect(try! latan(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(-1.1071487177940904 0.0)")
  inspect(try! latan(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(-1.1071487177940904 -0.0)")
  inspect(try! latan(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(1.421546861001807 -0.5003700000525311)")
  inspect(try! latan(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(1.0172219678978514 0.40235947810852507)")
  inspect(try! latan(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(1.0e-170 1.0e-170)")
  inspect(try! latan(Value::Cplx(Value::Flo(1.0e200), Value::Flo(1.0e200))), content="#C(1.5707963267948966 5.0e-201)")
  inspect(try! latan(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(0.847575660670829 0.2388778612568591)")
  inspect(try! latan(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(-1.4993442749903219 0.3060541966472516)")
  inspect(try! latan(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(1.5707963267948966 0.5493061443340549)")
  inspect(try! latan(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(1.5707963267948966 -0.5493061443340549)")
  inspect(try! latan(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(-0.8760580505981934 -0.0)")
  inspect(try! latan(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(1.568296472618543 1.8748828207025026e-5)")
  inspect(try! latan(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(0.0 -1.843185350795686)")
  inspect(try! latan(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(1.3752985910711983 0.28184302887940405)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(0.3189624333048183 0.3903162045220237)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(1.5285709194809982 0.4270785863924761)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(-1.8184464592320668 -3.1622776601683794e-301)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(1.3258977669011374 0.0)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(-1.4436354751788103 0.0)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(-1.4436354751788103 -0.0)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(1.3618009008578458 -1.2930420702371825)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(1.0612750619050357 0.6662394324925153)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(1.0e-170 1.0e-170)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(1.0e200), Value::Flo(1.0e200))), content="#C(461.55673936964905 0.7853981633974483)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(0.9261330313501823 0.3494390628572133)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(-1.8579562931236187 1.3450496524056388)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(1.3169578969248166 1.5707963267948966)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(-1.3169578969248166 -1.5707963267948966)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(-1.015973134179692 -0.0)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(6.684641414109634 0.007499835944992231)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(0.0 -1.2567777313870419)")
  inspect(try! lasinh(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(1.7666320810508114 0.9734901163934966)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(0.4051123371780309 1.2901667645030908)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(1.4693517443681852 0.5073563032171445)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(1.762747174039086 -3.141592653589793)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(1.158810360429947 0.0)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(1.3169578969248166 3.141592653589793)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(-1.3169578969248166 -3.141592653589793)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(1.4657153519472905 -1.3497776911720127)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(1.0612750619050357 0.9045568943023813)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(1.0e-170 1.5707963267948966)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(1.0e200), Value::Flo(1.0e200))), content="#C(461.55673936964905 0.7853981633974484)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(0.7328576759736453 0.6748888455860064)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(1.9003216649977321 1.7770058678873573)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(1.4436354751788103 1.5707963267948966)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(1.4436354751788103 -1.5707963267948966)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(-0.6223625037147786 -3.141592653589793)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(6.684638289636928 0.007499882814719241)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(0.8463699602485695 -1.5707963267948966)")
  inspect(try! lacosh(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(1.7903012744337676 1.0253898445471405)")
  inspect(try! latanh(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(0.26149213879567196 0.4088225229163512)")
  inspect(try! latanh(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(0.40235947810852507 1.3389725222944935)")
  inspect(try! latanh(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(-0.34657359027997264 -1.5707963267948966)")
  inspect(try! latanh(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(0.6496414920651304 1.5707963267948966)")
  inspect(try! latanh(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(-0.5493061443340549 1.5707963267948966)")
  inspect(try! latanh(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(-0.5493061443340549 -1.5707963267948966)")
  inspect(try! latanh(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(0.09641562020299617 -1.1265564408348223)")
  inspect(try! latanh(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(0.40235947810852507 1.0172219678978514)")
  inspect(try! latanh(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(1.0e-170 1.0e-170)")
  inspect(try! latanh(Value::Cplx(Value::Flo(1.0e200), Value::Flo(1.0e200))), content="#C(5.0e-201 1.5707963267948966)")
  inspect(try! latanh(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(0.7083033360140539 0.9078874949608804)")
  inspect(try! latanh(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(-0.059961851295789396 1.2798909606873992)")
  inspect(try! latanh(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(0.0 1.1071487177940904)")
  inspect(try! latanh(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(0.0 -1.1071487177940904)")
  inspect(try! latanh(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(-1.1989476363991853 -1.5707963267948966)")
  inspect(try! latanh(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(0.002499864589504994 1.5707775777323585)")
  inspect(try! latanh(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(0.0 -0.7603406115491446)")
  inspect(try! latanh(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(0.17010239370256466 1.2852522702597784)")
  inspect(try! ltan(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(0.261073681841663 0.41063347084255636)")
  inspect(try! ltan(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(-0.24345820118572525 1.1667362572409197)")
  inspect(try! ltan(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(0.1425465430742778 -1.020319516942427e-300)")
  inspect(try! ltan(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(-5.52037992250933 0.0)")
  inspect(try! ltan(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(2.185039863261519 0.0)")
  inspect(try! ltan(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(2.185039863261519 -0.0)")
  inspect(try! ltan(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(0.030215987322877575 -0.9799408499617379)")
  inspect(try! ltan(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(0.27175258531951174 1.0839233273386943)")
  inspect(try! ltan(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(1.0e-170 1.0e-170)")
  inspect(try! ltan(Value::Cplx(Value::Flo(1.0e200), Value::Flo(1.0e200))), content="#C(1.0 1.0)")
  inspect(try! ltan(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(0.806877412163085 1.042830728344361)")
  inspect(try! ltan(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(-0.003272904693711929 0.9994299817014717)")
  inspect(try! ltan(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(0.0 0.9640275800758169)")
  inspect(try! ltan(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(0.0 -0.9640275800758169)")
  inspect(try! ltan(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(-2.5721516221263183 -0.0)")
  inspect(try! ltan(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(0.004441698783744904 1.0022142111467482)")
  inspect(try! ltan(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(0.0 -0.7402806285799371)")
  inspect(try! ltan(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(-7.396495287915176e-4 1.013832722141065)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(0.3382547432654715 0.3811320742724429)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(1.0147936161466333 0.03381282607989669)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(-0.9950547536867306 -9.86603716544019e-303)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(0.9413755384972873 0.0)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(-0.9640275800758169 0.0)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(-0.9640275800758169 -0.0)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(1.3212865837711916 0.8508781211449377)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(1.0839233273386943 0.27175258531951174)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(1.0e-170 1.0e-170)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(1.0e200), Value::Flo(1.0e200))), content="#C(1.0 1.0)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(0.8429662048457831 0.19557731006593398)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(-0.6056777981941319 0.037069374634907525)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(0.0 -2.185039863261519)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(0.0 2.185039863261519)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(-0.8336546070121552 -0.0)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(1.0 1.0)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(0.0 -1.4016385500601853)")
  inspect(try! ltanh(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(0.9755896814927838 -0.07725907307588284)")
  inspect(try! lexp(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(1.2433022950695027 0.5256597791969788)")
  inspect(try! lexp(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(3.992324048441272 6.217676312367968)")
  inspect(try! lexp(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(0.049787068367863944 -4.978706836786395e-302)")
  inspect(try! lexp(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(5.754602676005731 0.0)")
  inspect(try! lexp(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(0.1353352832366127 0.0)")
  inspect(try! lexp(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(0.1353352832366127 -0.0)")
  inspect(try! lexp(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(-0.6861101411498431 -1.4991780090003948)")
  inspect(try! lexp(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(1.4686939399158851 2.2873552871788423)")
  inspect(try! lexp(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(1.0 1.0e-170)")
  inspect(try! lexp(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(2.3855167309591354 1.3032137296869954)")
  inspect(try! lexp(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(-0.49573851451141454 -0.02898774174754817)")
  inspect(try! lexp(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(-0.4161468365471424 0.9092974268256817)")
  inspect(try! lexp(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(-0.4161468365471424 -0.9092974268256817)")
  inspect(try! lexp(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(0.30119421191220214 -0.0)")
  inspect(try! lexp(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(-5.169215814093158e173 7.368538447038685e172)")
  inspect(try! lexp(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(0.5807879999714659 -0.8140548501723606)")
  inspect(try! lexp(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(-3.926717383396283 2.9970672974149126)")
  inspect(try! lsin(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(0.31947873074156463 0.3924066848326388)")
  inspect(try! lsin(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(1.4031192506220405 -0.4890562590412937)")
  inspect(try! lsin(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(-0.1411200080598672 9.899924966004455e-301)")
  inspect(try! lsin(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(0.9839859468739369 -0.0)")
  inspect(try! lsin(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(-0.9092974268256817 -0.0)")
  inspect(try! lsin(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(-0.9092974268256817 0.0)")
  inspect(try! lsin(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(1.8036926955321817 -3.182869448337149)")
  inspect(try! lsin(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(1.2984575814159773 0.6349639147847361)")
  inspect(try! lsin(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(1.0e-170 1.0e-170)")
  inspect(try! lsin(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(0.948864531437168 0.28154899513533443)")
  inspect(try! lsin(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(-7.915274799222129 9.366168701165266)")
  inspect(try! lsin(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(0.0 3.6268604078470186)")
  inspect(try! lsin(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(0.0 -3.6268604078470186)")
  inspect(try! lsin(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(-0.9320390859672263 -0.0)")
  inspect(try! lsin(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(-8.56676849851089 -5.262353020347283)")
  inspect(try! lsin(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(0.0 -1.1011197960579648)")
  inspect(try! lsin(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(6.067953288287812 -0.15879907485272157)")
  inspect(try! lcos(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(1.032787884202841 -0.12138561220787392)")
  inspect(try! lcos(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(-0.64214812471552 -1.0686074213827783)")
  inspect(try! lcos(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(-0.9899924966004454 -1.4112000805986721e-301)")
  inspect(try! lcos(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(-0.17824605564949209 -0.0)")
  inspect(try! lcos(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(-0.4161468365471424 0.0)")
  inspect(try! lcos(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(-0.4161468365471424 -0.0)")
  inspect(try! lcos(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(3.3016373329140944 1.7388095044743164)")
  inspect(try! lcos(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(0.8337300251311491 -0.9888977057628651)")
  inspect(try! lcos(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(1.0 -0.0)")
  inspect(try! lcos(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(0.6092589091577942 -0.4384865798925953)")
  inspect(try! lcos(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(9.397345354414616 7.889015066448475)")
  inspect(try! lcos(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(3.7621956910836314 -0.0)")
  inspect(try! lcos(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(3.7621956910836314 0.0)")
  inspect(try! lcos(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(0.3623577544766736 -0.0)")
  inspect(try! lcos(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(-5.288505985072667 8.524403718176996)")
  inspect(try! lcos(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(1.4874356474384813 0.0)")
  inspect(try! lcos(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(-0.16099885791134794 -5.985044744604468)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(0.2804817641764754 0.4070739913234487)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(1.959601041421606 3.165778513216168)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(-10.017874927409903 -1.0067661995777766e-299)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(2.7904143662776426 0.0)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(-3.6268604078470186 0.0)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(-3.6268604078470186 -0.0)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(-0.21685216292078974 -1.0253473885839877)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(0.6349639147847361 1.2984575814159773)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(1.0e-170 1.0e-170)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(1.0313360742545512 0.7397922644560138)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(0.7572901465494509 -0.07326941556055375)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(-0.0 0.9092974268256817)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(-0.0 -0.9092974268256817)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(-1.5094613554121725 -0.0)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(-2.584607907046579e173 3.684269223519342e172)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(0.0 -0.8140548501723606)")
  inspect(try! lsinh(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(-1.8828981897569583 1.5599451320296758)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(0.3), Value::Flo(0.4))), content="#C(0.9628205308930272 0.11858578787353008)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0))), content="#C(2.0327230070196656 3.0518977991517997)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(-3.0), Value::Flo(-1.0e-300))), content="#C(10.067661995777765 1.0017874927409903e-299)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(1.75), Value::Flo(0.0))), content="#C(2.9641883097280877 0.0)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.0))), content="#C(3.7621956910836314 -0.0)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(-2.0), Value::Flo(-0.0))), content="#C(3.7621956910836314 0.0)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(0.5), Value::Flo(-2.0))), content="#C(-0.4692579782290534 -0.473830620416407)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0))), content="#C(0.8337300251311491 0.9888977057628651)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(1.0e-170), Value::Flo(1.0e-170))), content="#C(1.0 0.0)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(1.0), Value::Flo(0.5))), content="#C(1.3541806567045842 0.5634214652309818)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(-0.7), Value::Flo(3.2))), content="#C(-1.2530286610608654 0.04428167381300557)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(0.0), Value::Flo(2.0))), content="#C(-0.4161468365471424 0.0)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(0.0), Value::Flo(-2.0))), content="#C(-0.4161468365471424 -0.0)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(-1.2), Value::Flo(-0.0))), content="#C(1.8106555673243747 0.0)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(400.0), Value::Flo(3.0))), content="#C(-2.584607907046579e173 3.684269223519342e172)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(0.0), Value::Flo(-0.9510999762907357))), content="#C(0.5807879999714659 -0.0)")
  inspect(try! lcosh(Value::Cplx(Value::Flo(1.5973227494865936), Value::Flo(2.4896652952199303))), content="#C(-2.043819193639325 1.4371221653852368)")
  inspect(try! llog(Value::Flo(2.0)), content="0.6931471805599453")
  inspect(try! llog(Value::Flo(-3.0)), content="#C(1.0986122886681098 3.141592653589793)")
  inspect(try! llog(Value::Flo(0.5)), content="-0.6931471805599453")
  inspect(try! llog(Value::Flo(-0.5)), content="#C(-0.6931471805599453 3.141592653589793)")
  inspect(try! llog(Value::Flo(-1.5)), content="#C(0.4054651081081644 3.141592653589793)")
  inspect(try! lsqrt(Value::Flo(2.0)), content="1.4142135623730951")
  inspect(try! lsqrt(Value::Flo(-3.0)), content="#C(0.0 1.7320508075688772)")
  inspect(try! lsqrt(Value::Flo(0.5)), content="0.7071067811865476")
  inspect(try! lsqrt(Value::Flo(-0.5)), content="#C(0.0 0.7071067811865476)")
  inspect(try! lsqrt(Value::Flo(-1.5)), content="#C(0.0 1.224744871391589)")
  inspect(try! lasin(Value::Flo(2.0)), content="#C(1.5707963267948966 -1.3169578969248166)")
  inspect(try! lasin(Value::Flo(-3.0)), content="#C(-1.5707963267948966 1.762747174039086)")
  inspect(try! lasin(Value::Flo(0.5)), content="0.5235987755982988")
  inspect(try! lasin(Value::Flo(-0.5)), content="-0.5235987755982988")
  inspect(try! lasin(Value::Flo(-1.5)), content="#C(-1.5707963267948966 0.9624236501192069)")
  inspect(try! lacos(Value::Flo(2.0)), content="#C(0.0 1.3169578969248166)")
  inspect(try! lacos(Value::Flo(-3.0)), content="#C(3.141592653589793 -1.762747174039086)")
  inspect(try! lacos(Value::Flo(0.5)), content="1.0471975511965976")
  inspect(try! lacos(Value::Flo(-0.5)), content="2.0943951023931957")
  inspect(try! lacos(Value::Flo(-1.5)), content="#C(3.141592653589793 -0.9624236501192069)")
  inspect(try! latan(Value::Flo(2.0)), content="1.1071487177940906")
  inspect(try! latan(Value::Flo(-3.0)), content="-1.2490457723982544")
  inspect(try! latan(Value::Flo(0.5)), content="0.46364760900080615")
  inspect(try! latan(Value::Flo(-0.5)), content="-0.46364760900080615")
  inspect(try! latan(Value::Flo(-1.5)), content="-0.982793723247329")
  inspect(try! lasinh(Value::Flo(2.0)), content="1.4436354751788103")
  inspect(try! lasinh(Value::Flo(-3.0)), content="-1.8184464592320668")
  inspect(try! lasinh(Value::Flo(0.5)), content="0.48121182505960347")
  inspect(try! lasinh(Value::Flo(-0.5)), content="-0.48121182505960347")
  inspect(try! lasinh(Value::Flo(-1.5)), content="-1.1947632172871094")
  inspect(try! lacosh(Value::Flo(2.0)), content="1.3169578969248166")
  inspect(try! lacosh(Value::Flo(-3.0)), content="#C(1.762747174039086 3.141592653589793)")
  inspect(try! lacosh(Value::Flo(0.5)), content="#C(0.0 1.0471975511965979)")
  inspect(try! lacosh(Value::Flo(-0.5)), content="#C(0.0 2.0943951023931953)")
  inspect(try! lacosh(Value::Flo(-1.5)), content="#C(0.9624236501192069 3.141592653589793)")
  inspect(try! latanh(Value::Flo(2.0)), content="#C(0.5493061443340549 1.5707963267948966)")
  inspect(try! latanh(Value::Flo(-3.0)), content="#C(-0.34657359027997264 1.5707963267948966)")
  inspect(try! latanh(Value::Flo(0.5)), content="0.5493061443340549")
  inspect(try! latanh(Value::Flo(-0.5)), content="-0.5493061443340549")
  inspect(try! latanh(Value::Flo(-1.5)), content="#C(-0.8047189562170501 1.5707963267948966)")
  inspect(try! ltan(Value::Flo(2.0)), content="-2.185039863261519")
  inspect(try! ltan(Value::Flo(-3.0)), content="0.1425465430742778")
  inspect(try! ltan(Value::Flo(0.5)), content="0.5463024898437905")
  inspect(try! ltan(Value::Flo(-0.5)), content="-0.5463024898437905")
  inspect(try! ltan(Value::Flo(-1.5)), content="-14.10141994717172")
  inspect(try! ltanh(Value::Flo(2.0)), content="0.9640275800758169")
  inspect(try! ltanh(Value::Flo(-3.0)), content="-0.9950547536867305")
  inspect(try! ltanh(Value::Flo(0.5)), content="0.46211715726000974")
  inspect(try! ltanh(Value::Flo(-0.5)), content="-0.46211715726000974")
  inspect(try! ltanh(Value::Flo(-1.5)), content="-0.9051482536448664")
  inspect(try! lexp(Value::Flo(2.0)), content="7.38905609893065")
  inspect(try! lexp(Value::Flo(-3.0)), content="0.049787068367863944")
  inspect(try! lexp(Value::Flo(0.5)), content="1.6487212707001282")
  inspect(try! lexp(Value::Flo(-0.5)), content="0.6065306597126334")
  inspect(try! lexp(Value::Flo(-1.5)), content="0.22313016014842982")
  inspect(try! lsin(Value::Flo(2.0)), content="0.9092974268256817")
  inspect(try! lsin(Value::Flo(-3.0)), content="-0.1411200080598672")
  inspect(try! lsin(Value::Flo(0.5)), content="0.479425538604203")
  inspect(try! lsin(Value::Flo(-0.5)), content="-0.479425538604203")
  inspect(try! lsin(Value::Flo(-1.5)), content="-0.9974949866040544")
  inspect(try! lcos(Value::Flo(2.0)), content="-0.4161468365471424")
  inspect(try! lcos(Value::Flo(-3.0)), content="-0.9899924966004454")
  inspect(try! lcos(Value::Flo(0.5)), content="0.8775825618903728")
  inspect(try! lcos(Value::Flo(-0.5)), content="0.8775825618903728")
  inspect(try! lcos(Value::Flo(-1.5)), content="0.0707372016677029")
  inspect(try! lsinh(Value::Flo(2.0)), content="3.6268604078470186")
  inspect(try! lsinh(Value::Flo(-3.0)), content="-10.017874927409903")
  inspect(try! lsinh(Value::Flo(0.5)), content="0.5210953054937474")
  inspect(try! lsinh(Value::Flo(-0.5)), content="-0.5210953054937474")
  inspect(try! lsinh(Value::Flo(-1.5)), content="-2.1292794550948173")
  inspect(try! lcosh(Value::Flo(2.0)), content="3.7621956910836314")
  inspect(try! lcosh(Value::Flo(-3.0)), content="10.067661995777765")
  inspect(try! lcosh(Value::Flo(0.5)), content="1.1276259652063807")
  inspect(try! lcosh(Value::Flo(-0.5)), content="1.1276259652063807")
  inspect(try! lcosh(Value::Flo(-1.5)), content="2.352409615243247")
}

///|
test "expt like sbcl" {
  inspect(try! expt(Value::Cplx(Value::Flo(1.0), Value::Flo(1.0)), Value::Fix(2L)), content="#C(1.2246467991473535e-16 2.0000000000000004)")
  inspect(try! expt(Value::Cplx(Value::Flo(1.1), Value::Flo(0.3)), Value::Fix(7L)), content="#C(-0.7234215999999998 2.398231200000001)")
  inspect(try! expt(Value::Cplx(Value::Flo(1.1), Value::Flo(0.3)), Value::Fix(-3L)), content="#C(0.4706417842512516 -0.4833864360491579)")
  inspect(try! expt(Value::Cplx(Value::Flo(1.1), Value::Flo(0.3)), Value::Fix(0L)), content="#C(1.0 0.0)")
  inspect(try! expt(Value::Flo(-2.0), Value::Flo(0.5)), content="#C(8.659560562354934e-17 1.4142135623730951)")
  inspect(try! expt(Value::Flo(-2.0), try! num_div(Value::Fix(1L), Value::Fix(3L))), content="#C(0.6299605249474367 1.0911236359717214)")
  inspect(try! expt(Value::Flo(2.0), try! num_div(Value::Fix(1L), Value::Fix(3L))), content="1.2599210498948732")
  inspect(try! expt(Value::Flo(-8.0), Value::Flo(2.0)), content="64.0")
  inspect(try! expt(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0)), Value::Flo(0.5)), content="#C(1.455346690225355 0.34356074972251244)")
  inspect(try! expt(Value::Cplx(Value::Flo(2.0), Value::Flo(1.0)), Value::Cplx(Value::Flo(0.5), Value::Flo(0.25))), content="#C(1.208786251938855 0.558775149613474)")
  inspect(try! expt(Value::Flo(2.0), Value::Cplx(Value::Flo(0.5), Value::Flo(0.25))), content="#C(1.3930334183655622 0.24383989689293284)")
  inspect(try! expt(Value::Flo(-2.0), Value::Cplx(Value::Flo(0.5), Value::Flo(0.25))), content="#C(-0.11117590606401737 0.6351370486850603)")
  inspect(try! expt(Value::Cplx(Value::Flo(-2.0), Value::Flo(0.5)), try! num_div(Value::Fix(1L), Value::Fix(3L))), content="#C(0.7241429673663325 1.0466245092929098)")
  inspect(try! expt(Value::Fix(3L), Value::Cplx(Value::Flo(1.0), Value::Flo(2.0))), content="#C(-1.7587648028740572 2.430379881452976)")
  inspect(try! expt(Value::Flo(0.0), Value::Cplx(Value::Flo(1.0), Value::Flo(2.0))), content="#C(0.0 0.0)")
  inspect(try! expt(Value::Cplx(Value::Flo(1.0), Value::Flo(2.0)), Value::Flo(0.0)), content="#C(1.0 0.0)")
  inspect(try! num_sub(Value::Cplx(Value::Flo(2.0), Value::Flo(-0.0)), Value::Fix(1L)), content="#C(1.0 -0.0)")
  inspect(try! num_sub(Value::Fix(1L), Value::Cplx(Value::Flo(2.0), Value::Flo(-0.0))), content="#C(-1.0 0.0)")
}

///|
test "eq on bignums is identity" {
  let b = try! expt(Fix(10L), Fix(30L))
  inspect(eq(b, b), content="true")
  inspect(eq(b, try! expt(Fix(10L), Fix(30L))), content="false")
}

///|
test "subnormal printing like sbcl" {
  inspect(float_to_string(4.9406564584124654e-324), content="4.9406564584124654e-324")
  inspect(float_to_string(1.0e-310), content="9.99999999999997e-311")
  inspect(float_to_string(1.5e-315), content="1.500000000192854e-315")
  inspect(float_to_string(3.0 * 4.9406564584124654e-324), content="1.4821969375237396e-323")
  inspect(float_to_string(2.2250738585072014e-308), content="2.2250738585072014e-308")
}

///|
test "real / complex like sbcl two-arg-/" {
  inspect(try! num_div(Value::Flo(57.156235665862923517), Value::Cplx(Value::Flo(2.2999999999999998), Value::Flo(1.7))), content="#C(16.07082420922796 -11.878435285081538)")
  inspect(try! num_div(Value::Flo(-2.0), Value::Cplx(Value::Flo(3.0), Value::Flo(-7.0))), content="#C(-0.10344827586206898 -0.24137931034482762)")
  inspect(try! num_div(Value::Flo(0.0), Value::Cplx(Value::Flo(3.0), Value::Flo(-7.0))), content="#C(-0.0 0.0)")
  inspect(try! num_div(Value::Flo(-0.0), Value::Cplx(Value::Flo(3.0), Value::Flo(7.0))), content="#C(0.0 0.0)")
}

///|
test "libm overflow traps like sbcl" {
  let f = (thunk : () -> Value raise LispError) => {
    let r = try thunk() catch { e => Value::Str("\{e}") } noraise { v => v }
    r
  }
  inspect(f(() => lexp(Value::Flo(1000.0))), content="\"floating-point-overflow: arithmetic error FLOATING-POINT-OVERFLOW signalled\"")
  inspect(f(() => lexp(Value::Cplx(Value::Flo(1000.0), Value::Flo(1.0)))), content="\"floating-point-overflow: arithmetic error FLOATING-POINT-OVERFLOW signalled\"")
  inspect(f(() => lsin(Value::Cplx(Value::Flo(1.0), Value::Flo(1000.0)))), content="\"floating-point-overflow: arithmetic error FLOATING-POINT-OVERFLOW signalled\"")
  inspect(f(() => lexp(Value::Flo(-1000.0))), content="0.0")
  inspect(f(() => latanh(Value::Flo(1.0))), content="\"division-by-zero: arithmetic error DIVISION-BY-ZERO signalled\"")
}

///|
test "expt double negative integer is pow" {
  inspect(try! expt(Value::Flo(2.0), Fix(-1075L)), content="0.0")
  inspect(try! expt(Value::Flo(2.0), Fix(-1074L)), content="4.9406564584124654e-324")
}

///|
test "format ~d non-integer like sbcl" {
  inspect(try! format_to_string("~10,'0d|", [Value::Str("42")]), content="42|")
  inspect(try! format_to_string("~5d|", [Value::Flo(1.5)]), content="1.5|")
  inspect(try! format_to_string("~5d|", [int(42)]), content="   42|")
}

///|
test "rationalize and ratio->double like sbcl" {
  inspect(try! rationalize(Value::Flo(0.1)), content="1/10")
  inspect(try! rationalize(Value::Flo(3.14159)), content="314159/100000")
  inspect(try! rationalize(Value::Flo(-2.5)), content="-5/2")
  inspect(try! rationalize(Value::Flo(1.0e20)), content="100000000000000000000")
  let p54 = 1N.shl(54)
  inspect(Value::Flo(ratio_to_double(p54 + 1N, 1N.shl(1129))), content="4.9406564584124654e-324")
  inspect(Value::Flo(ratio_to_double(p54 * 3N - 1N, 1N.shl(1129))), content="4.9406564584124654e-324")
  inspect(Value::Flo(ratio_to_double(1N, 3N)), content="0.3333333333333333")
}

///|
test "rationalize subnormal like sbcl" {
  let r = try! rationalize(Value::Flo(1.0e-310))
  inspect(
    r,
    content="1/10000000000000029585700532568710905412162044573659127867256961394138855916216577035990592132781655066040632299219124298160699847459562696640056798183800907088924439778379480018907727530761128912150211171876367354579208524858715189730041035925482684218362104686626453532566663427340026346067178972764032033222344",
  )
}

///|
test "format ~E ~G like sbcl" {
  inspect(
    try! format_to_string("~,1E|~,1E|~,2E|~,2E|~,0E|~E", [
      Value::Flo(0.125), Value::Flo(0.375), Value::Flo(1.999), Value::Flo(9.999), Value::Flo(2.5), Value::Flo(1.999),
    ]),
    content="1.3e-1|3.8e-1|2.00e+0|10.00e+0|3.e+0|1.999e+0",
  )
  inspect(
    try! format_to_string("~,2G|~,3G|~G|~,2G|~,2G|~8,2G|", [
      Value::Flo(1.999), Value::Flo(1234.5), Value::Flo(1.999), Value::Flo(0.05), Value::Flo(123456.0), Value::Flo(3.5),
    ]),
    content="2.0    |1.235e+3|1.999    |5.00e-2|1.23e+5| 3.5    |",
  )
  inspect(
    try! format_to_string("~,2E|~,2E|~10,2E|~,3E", [
      Value::Flo(0.0), Value::Flo(-1.5e10), Value::Flo(1.5e-5), Value::Flo(123.456),
    ]),
    content="0.00e+0|-1.50e+10|   1.50e-5|1.235e+2",
  )
}

///|
test "process primitives" {
  inspect(run_shell_command("exit 3"), content="3")
  inspect(shell_command_output("printf hello"), content="(0, hello)")
  assert_true(current_directory().length() > 0)
}

///|
test "output file streams" {
  let path = "_build/runtime_test_output_file.txt"
  let s = open_output_file(path)
  write_string("ab", stream=s)
  terpri(stream=s)
  inspect(stream_column(stream=s), content="0")
  write_string("ü", stream=s)
  inspect(read_file(path), content="ab\nü")
  // :if-exists :append keeps the contents; the default supersedes them
  let s2 = open_output_file(path, append=true)
  write_string("c", stream=s2)
  inspect(read_file(path), content="ab\nüc")
  let _ = open_output_file(path)
  inspect(read_file(path), content="")
  append_file(path, "x")
  inspect(read_file(path), content="x")
}

///|
test "input designator t reads the terminal, not *standard-input*" {
  let saved = console_reader.val
  console_reader.val = () => Some("ab")
  let got = with_special(
    standard_input,
    make_string_input_stream("xy"),
    () => list([read_char(stream=t), read_char(), read_char(stream=t)]),
  ) catch {
    _ => Nil
  }
  console_reader.val = saved
  inspect(prin1_to_string(got), content="(#\\a #\\x #\\b)")
}

///|
test "binary file output round trip" {
  let path = "_build/runtime_test_bytes.bin"
  let data = Bytes::from_array([b'R', b'I', b'F', b'F', b'\x00', b'\xff', b'\x80'])
  write_file_bytes(path, data) catch {
    _ => fail("write_file_bytes failed")
  }
  let back = read_file_bytes(path) catch { _ => b"" }
  inspect(back.length(), content="7")
  inspect(back[5].to_int(), content="255")
  assert_true(back == data)
}

///|
test "format radix directives print upper-case digits" {
  inspect(
    try! format_to_string("&#x~x;|~16r|~b", [int(60), int(255), int(5)]),
    content="&#x3C;|FF|101",
  )
}

///|
test "princ of a keyword omits the colon" {
  inspect(princ_to_string(Sym(intern(":rational"))), content="rational")
  inspect(prin1_to_string(Sym(intern(":rational"))), content=":rational")
}
