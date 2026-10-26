// Port of src/psolve.lisp: explicit solutions of cubic and quartic
// polynomials (called from SOLVE1A in solve.lisp).

///|
fn psolve__rat(n : Int64, d : Int64) -> Value {
  mk_simp(q_rat, [Fix(n), Fix(d)])
}

///|
fn solvecubic(x : Value) -> Value raise {
  let x = cdr(x)
  let lcoef = cadr(x)
  let mut a2 = ratreduce(ptterm(x, Fix(2L)), lcoef)
  let adiv3 = mul2(psolve__rat(-1L, 3L), simplify(rdis(a2)))
  let mut a1 = ratreduce(ptterm(x, Fix(1L)), lcoef)
  let mut a0 = ratreduce(ptterm(x, Fix(0L)), lcoef)

  // coefficients now a0,a1,a2,  and leading coef 1.
  a2 = simplify(rdis(a2))
  a1 = simplify(rdis(a1))
  a0 = simplify(rdis(a0))
  let s1 = mul3(
    psolve__rat(1L, 2L),
    q_d__pcti,
    power(Fix(3L), psolve__rat(1L, 2L)),
  )
  let omega = add2(psolve__rat(-1L, 2L), s1)
  let omega_hat2 = add2(psolve__rat(-1L, 2L), mul2(Fix(-1L), s1))
  let pdiv3 = add2(
    mul2(a1, psolve__rat(1L, 3L)),
    mul2(power(a2, Fix(2L)), psolve__rat(-1L, 9L)),
  )
  let mult = () => symval(q_mult)
  if equal(sratsimp(pdiv3), Fix(0L)) {
    let y2 = add2(power(a2, Fix(3L)), mul2(Fix(-27L), a0))
    let y1 = mul2(
      psolve__rat(1L, 3L),
      add2(simpnrt(y2, Fix(3L)), mul2(Fix(-1L), a2)), // cube root
    )
    if symval(q_flag4).truthy() {
      return solve3(y1, mult())
    }
    let y2 = simpnrt(mul2(y2, psolve__rat(1L, 27L)), Fix(3L))
    return mapc(
      j => solve3(j, mult()) |> ignore,
      list([y1, add2(mul2(omega, y2), adiv3), add2(mul2(omega_hat2, y2), adiv3)]),
    )
  }
  // harder
  let qdiv_2 = add2(
    mul2(add2(mul2(a1, a2), mul2(Fix(-3L), a0)), psolve__rat(1L, 6L)),
    mul2(power(a2, Fix(3L)), psolve__rat(-1L, 27L)),
  )
  let mut u : Value = Nil
  let mut y1 : Value = Nil
  if equal(sratsimp(qdiv_2), Fix(0L)) {
    u = simpnrt(pdiv3, Fix(2L))
    y1 = adiv3
  } else {
    let mut discr = add2(power(pdiv3, Fix(3L)), power(qdiv_2, Fix(2L)))
    if equal(sratsimp(discr), Fix(0L)) {
      u = simpnrt(qdiv_2, Fix(3L))
    } else {
      discr = simpnrt(discr, Fix(2L))
      if complicated(discr).truthy() {
        discr = adispline(discr)
      }
      u = power(add2(qdiv_2, discr), psolve__rat(1L, 3L))
      if complicated(u).truthy() {
        u = adispline(u)
      }
    }
  }
  if equal(sratsimp(u), Fix(0L)) {
    merr("SOLVECUBIC: arithmetic overflow.", []) |> ignore
  }
  if !y1.truthy() {
    y1 = addn_([adiv3, u, mul3(Fix(-1L), pdiv3, power(u, Fix(-1L)))])
  }
  if symval(q_flag4).truthy() {
    solve3(y1, mult())
  } else {
    mapc(
      j => solve3(j, mult()) |> ignore,
      list([
        y1,
        addn_([
          adiv3,
          mul2(omega, u),
          muln_([Fix(-1L), pdiv3, omega_hat2, power(u, Fix(-1L))]),
        ]),
        addn_([
          adiv3,
          mul2(omega_hat2, u),
          muln_([Fix(-1L), pdiv3, omega, power(u, Fix(-1L))]),
        ]),
      ]),
    )
  }
}

///|
fn solvequartic(x : Value) -> Value raise {
  let x = cdr(x)
  let lcoef = cadr(x)
  let b3 = simplify(rdis(ratreduce(ptterm(x, Fix(3L)), lcoef)))
  let b2 = simplify(rdis(ratreduce(ptterm(x, Fix(2L)), lcoef)))
  let b1 = simplify(rdis(ratreduce(ptterm(x, Fix(1L)), lcoef)))
  let b0 = simplify(rdis(ratreduce(ptterm(x, Fix(0L)), lcoef)))
  let mut a2 = mul2(Fix(-1L), b2)
  let mut a0 = mul2(b0, Fix(4L))
  let mut a1 = sub(mul2(b1, b3), a0)
  let sqb3 = power(b3, Fix(2L))
  a0 = sub(sub(mul2(b2, a0), mul2(sqb3, b0)), power(b1, Fix(2L)))
  let mut tr2 = mul2(
    psolve__rat(1L, 4L),
    sub(sub(mul3(b3, b2, Fix(4L)), mul2(Fix(8L), b1)), mul2(sqb3, b3)),
  )
  let mut z1 = resolvent(a2, a1, a0)
  let mut r = add2(z1, sub(mul2(sqb3, psolve__rat(1L, 4L)), b2))
  r = simpnrt(r, Fix(2L))
  let mut tr1 : Value = Nil
  if equal(sratsimp(r), Fix(0L)) {
    // l0
    let d1 = simpnrt(add2(power(z1, Fix(2L)), mul2(Fix(-4L), b0)), Fix(2L))
    tr2 = mul2(Fix(2L), d1)
    if complicated(tr2).truthy() {
      tr2 = adispline(tr2)
    }
    tr1 = sub(mul2(sqb3, psolve__rat(3L, 4L)), mul2(b2, Fix(2L)))
    if complicated(tr1).truthy() {
      tr1 = adispline(tr1)
    }
  } else {
    if complicated(r).truthy() {
      r = adispline(r)
    }
    if complicated(tr2).truthy() {
      tr2 = adispline(tr2)
    }
    tr1 = sub(sub(mul2(sqb3, psolve__rat(1L, 2L)), b2), z1)
    if complicated(tr1).truthy() {
      tr1 = adispline(tr1)
    }
    tr2 = div_star(tr2, r)
  }
  // lb1
  let mut d = div(power(add2(tr1, tr2), psolve__rat(1L, 2L)), Fix(2L))
  let mut e = div(power(sub(tr1, tr2), psolve__rat(1L, 2L)), Fix(2L))
  if complicated(d).truthy() {
    d = adispline(d)
  }
  if complicated(e).truthy() {
    e = adispline(e)
  }
  a2 = mul2(b3, psolve__rat(-1L, 4L))
  a1 = div_star(r, Fix(2L))
  z1 = list([
    addn_([a2, a1, d]), //1
    addn_([a2, a1, mul2(Fix(-1L), d)]), //2
    addn_([a2, mul2(Fix(-1L), a1), e]), //3
    addn_([a2, mul2(Fix(-1L), a1), mul2(Fix(-1L), e)]), //4
  ])
  mapc(j => solve3(j, symval(q_mult)) |> ignore, z1)
}

///|
/// SOLVES RESOLVENT CUBIC EQUATION GENERATED FROM QUARTIC
fn resolvent(a2 : Value, a1 : Value, a0 : Value) -> Value raise {
  with_specials(
    [
      (q_n_starroots, Nil),
      (q_flag4, Nil),
      (q_n_starfailures, Nil),
      (q_d_solvefactors, Nil),
    ],
    () => {
      // undoes binding in algsys
      set(q_flag4, t) |> ignore
      set(q_d_solvefactors, t) |> ignore
      let yy = gensym()
      solve(
        addn_([
          power(yy, Fix(3L)),
          mul2(a2, power(yy, Fix(2L))),
          mul2(a1, yy),
          a0,
        ]),
        yy,
        Fix(1L),
      )
      |> ignore
      if member_equal(Fix(0L), symval(q_n_starroots)).truthy() {
        return Fix(0L)
      }
      caddar(cdr(reverse(symval(q_n_starroots))))
    },
  )
}

///|
fn init_psolve() -> Unit raise {
  ()
}
