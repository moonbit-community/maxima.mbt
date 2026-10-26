// Port of src/compar.lisp, part 2: equality (MEQP) and order predicates, and
// the core of the sign machinery: SIGN1, SIGN and the handlers for products,
// sums and powers.

///|
/// Other than sums, products, and lambda forms, meqp knows nothing about dummy
/// variables; niceindices canonicalizes those of sums and products.
fn meqp_by_csign(z : Value, a : Value, b : Value) -> Value raise {
  let mut z = z
  // $NICEINDICES completely rebuilds the expression; only pay that price
  // when it actually contains a sum or product.
  if amongl(list2(q_p_sum, q_p_product), z).truthy() {
    let zz = z
    z = with_special(
      q_d_niceindicespref,
      list([list1(q_mlist), gensym(), gensym(), gensym()]),
      () => d_niceindices(zz),
    )
  }
  z = if d_constantp(z).truthy() { d_rectform(z) } else { sratsimp(z) }
  let sgn = d_csign(z)
  let dunno = mk(q_d_equal, [a, b])
  if eq(q_d_zero, sgn) {
    t
  } else if compar__in(sgn, [q_d_pos, q_d_neg, q_d_pn]) {
    Nil
  } else if compar__in(sgn, [q_d_complex, q_d_imaginary]) {
    // TRISPLIT goes back to general evaluation and could recurse forever;
    // WITH-SAFE-RECURSION guards against that.
    let zz = z
    call_with_safe_recursion(
      q_meqp_by_csign,
      zz,
      lfunc("meqp-by-csign", fn(_args : Array[Value]) -> Value raise {
        let ri_parts = trisplit(zz)
        // No need to call $CSIGN again on realpart(Z) if that's just Z.
        let rsgn : Value = if alike1(car(ri_parts), zz).truthy() {
          Nil
        } else {
          d_csign(car(ri_parts))
        }
        let isgn = if zerop1(cdr(ri_parts)).truthy() {
          q_d_zero
        } else {
          d_csign(cdr(ri_parts))
        }
        if eq(q_d_zero, rsgn) && eq(q_d_zero, isgn) {
          t
        } else if compar__in(rsgn, [q_d_neg, q_d_pos, q_d_pn]) ||
          compar__in(isgn, [q_d_neg, q_d_pos, q_d_pn]) {
          Nil
        } else {
          dunno
        }
      }),
    ) catch {
      LispError::Condition(s, _, _) if s.name == "unsafe-recursion" => dunno
      e => raise e
    }
  } else {
    dunno
  }
}

///|
/// For each fact of the form equal(a,b) in the active context, do
/// e : ratsubst(b,a,e).
fn equal_facts_simp(e : Value) -> Value raise {
  let mut e = e
  for fi in margs(d_facts()).iter() {
    if op_equalp(fi, list1(q_d_equal)).truthy() {
      e = d_ratsubst(nth(2, fi), nth(1, fi), e)
    }
  }
  e
}

///|
fn maxima_declared_arrayp(x : Value) -> Value raise {
  if symbolp(x) && mget(x, q_array).truthy() {
    get(mget(x, q_array), q_array)
  } else {
    Nil
  }
}

///|
fn maxima_undeclared_arrayp(x : Value) -> Value raise {
  if symbolp(x) && mget(x, q_hashar).truthy() {
    get(mget(x, q_hashar), q_array)
  } else {
    Nil
  }
}

///|
/// A helper for MEQP. It must not call MEQP by itself!
fn provably_nonzero_p(e : Value) -> Value raise {
  if mnump(e).truthy() {
    lbool(!zerop1(e).truthy())
  } else if mtimesp(e).truthy() {
    lbool(every(x => provably_nonzero_p(x).truthy(), cdr(e)))
  } else if mexptp(e).truthy() {
    lbool(
      free_infp(e).truthy() &&
      (
        (mnump(third(e)).truthy() && mnegp(third(e)).truthy()) ||
        eq(t, mnqp(second(e), Fix(0L)))
      ),
    )
  } else {
    Nil
  }
}

///|
fn meqp(a : Value, b : Value, csign? : Value = t) -> Value raise {
  // Check for some particular types before falling into the general case.
  // With CSIGN = NIL, the final $CSIGN test is made only if SRATSIMP and
  // EQUAL-FACTS-SIMP rewrite A - B.
  if stringp(a) {
    lbool(stringp(b) && equal(a, b))
  } else if stringp(b) {
    Nil
  } else if arrayp(a) {
    if arrayp(b) {
      array_meqp(a, b)
    } else {
      Nil
    }
  } else if arrayp(b) {
    Nil
  } else if maxima_declared_arrayp(a).truthy() {
    if maxima_declared_arrayp(b).truthy() {
      maxima_declared_array_meqp(a, b)
    } else {
      Nil
    }
  } else if maxima_declared_arrayp(b).truthy() {
    Nil
  } else if maxima_undeclared_arrayp(a).truthy() {
    if maxima_undeclared_arrayp(b).truthy() {
      maxima_undeclared_array_meqp(a, b)
    } else {
      Nil
    }
  } else if maxima_undeclared_arrayp(b).truthy() {
    Nil
  } else {
    // Bind the SIGN specials: DCOMPARE sets them, and MEQP is called from
    // inside sign computations that must keep their own.
    compar__with_signs(fn() {
      let a = specrepcheck(a)
      let b = specrepcheck(b)
      let indefinites = symval(q_indefinites)
      let infinities = symval(q_ear_infinities)
      let sysconstp = (x : Value) => symbolp(x) &&
        (eq(t, x) || x is Nil || get(x, q_sysconst).truthy())
      if like(a, b).truthy() {
        lbool(member(a, indefinites) is Nil)
      } else if member(a, indefinites).truthy() ||
        member(b, indefinites).truthy() ||
        member(a, infinities).truthy() ||
        member(b, infinities).truthy() {
        Nil
      } else if sysconstp(a) && sysconstp(b) {
        Nil
      } else if mbagp(a).truthy() ||
        mrelationp(a).truthy() ||
        mbagp(b).truthy() ||
        mrelationp(b).truthy() {
        if (
            (mbagp(a).truthy() && mbagp(b).truthy()) ||
            (mrelationp(a).truthy() && mrelationp(b).truthy())
          ) &&
          eq(mop(a), mop(b)) &&
          length(margs(a)) == length(margs(b)) {
          let z = list_meqp(margs(a), margs(b))
          if eq(z, t) || z is Nil {
            z
          } else {
            mk(q_d_equal, [a, b])
          }
        } else {
          Nil
        }
      } else if op_equalp(a, list1(q_lambda)).truthy() &&
        op_equalp(b, list1(q_lambda)).truthy() {
        lambda_meqp(a, b)
      } else if d_setp(a).truthy() {
        set_meqp(a, b)
      } else if (zerop1(b).truthy() && provably_nonzero_p(a).truthy()) ||
        (zerop1(a).truthy() && provably_nonzero_p(b).truthy()) {
        // 0 isn't in the range of an exponential function, and a power with a
        // negative exponent is undefined at a zero base, not zero.
        Nil
      } else if mnump(a).truthy() && mnump(b).truthy() {
        // Two numbers: answer arithmetically (ZEROP1 uses float contagion).
        zerop1(sub(a, b))
      } else if dcompare(a, b).truthy() && eq(q_d_zero, compar__sign()) {
        // lookup in assumption database; dcompare sets sign
        t
      } else if compar__in(compar__sign(), [q_d_pos, q_d_neg, q_d_pn]) {
        Nil
      } else {
        // if database lookup failed, apply all equality facts
        let d = sub(a, b)
        let z = equal_facts_simp(sratsimp(d))
        if csign.truthy() || !alike1(z, d).truthy() {
          meqp_by_csign(z, a, b)
        } else {
          mk(q_d_equal, [a, b])
        }
      }
    })
  }
}

///|
fn compar__row_major_aref(a : Value, i : Int) -> Value raise {
  as_array(a).data[i]
}

///|
/// Two arrays are equal (according to MEQP) if they have the same dimensions
/// and their elements are MEQP.
fn array_meqp(p : Value, q : Value) -> Value raise {
  if !equal(array_dimensions(p), array_dimensions(q)) {
    return Nil
  }
  for i in 0..<array_total_size(p) {
    let z = with_special(q_d_ratprint, Nil, () => meqp(
      compar__row_major_aref(p, i),
      compar__row_major_aref(q, i),
    ))
    if z is Nil {
      return Nil
    } else if eq(z, t) {
      ()
    } else {
      return mk(q_d_equal, [p, q])
    }
  }
  t
}

///|
fn maxima_declared_array_meqp(p : Value, q : Value) -> Value raise {
  array_meqp(get(mget(p, q_array), q_array), get(mget(q, q_array), q_array))
}

///|
fn maxima_undeclared_array_meqp(p : Value, q : Value) -> Value raise {
  if alike1(
      mfuncall(q_d_arrayinfo, list1(p)),
      mfuncall(q_d_arrayinfo, list1(q)),
    ).truthy() {
    with_special(q_d_ratprint, Nil, () => meqp(
      d_listarray(p),
      d_listarray(q),
    ))
  } else {
    Nil
  }
}

///|
fn list_meqp(p : Value, q : Value) -> Value raise {
  if p is Nil || q is Nil {
    lbool(p is Nil && q is Nil)
  } else {
    let z = meqp(car(p), car(q))
    if z is Nil {
      Nil
    } else if eq(z, q_d_unknown) || op_equalp(z, list1(q_d_equal)).truthy() {
      // An unequal pair further on still makes P and Q unequal.
      if list_meqp(cdr(p), cdr(q)) is Nil {
        Nil
      } else {
        z
      }
    } else {
      list_meqp(cdr(p), cdr(q))
    }
  }
}

///|
fn lambda_meqp(a : Value, b : Value) -> Value raise {
  if length(second(a)) == length(second(b)) {
    let n = to_int(d_length(second(a)))
    let mut x : Value = Nil
    for _ in 0..<n {
      x = cons(gensym(), x)
    }
    x = cons(list1(q_mlist), x)
    let z = meqp(
      mfuncall(q_d_apply, list2(a, x)),
      mfuncall(q_d_apply, list2(b, x)),
    )
    if eq(t, z) || z is Nil {
      z
    } else {
      mk(q_d_equal, [a, b])
    }
  } else {
    Nil
  }
}

///|
fn set_meqp(a : Value, b : Value) -> Value raise {
  let aa = equal_facts_simp(a)
  let bb = equal_facts_simp(b)
  if !d_setp(bb).truthy() ||
    (d_emptyp(aa).truthy() && !d_emptyp(bb).truthy()) ||
    (d_emptyp(bb).truthy() && !d_emptyp(aa).truthy()) {
    return Nil
  }
  if length(aa) == length(bb) {
    let mut all = true
    let mut p = margs(aa)
    let mut q = margs(bb)
    while p is Cons(pc) && q is Cons(qc) {
      if !eq(t, meqp(pc.car, qc.car)) {
        all = false
        break
      }
      p = pc.cdr
      q = qc.cdr
    }
    if all {
      return t
    }
  }
  if set_not_eqp(margs(aa), margs(bb)).truthy() {
    Nil
  } else {
    mk(q_d_equal, [a, b])
  }
}

///|
fn set_not_eqp(a : Value, b : Value) -> Value raise {
  for ak in a.iter() {
    if every(s => meqp(ak, s) is Nil, b) {
      return t
    }
  }
  for bk in b.iter() {
    if every(s => meqp(bk, s) is Nil, a) {
      return t
    }
  }
  Nil
}

///|
/// MGRP-GENERAL applies when sign of A - B (possibly complex) makes sense.
fn mgrp_general(a : Value, b : Value) -> Value raise {
  let a = sub(a, b)
  let sgn = csign(a)
  if eq(sgn, q_d_pos) {
    t
  } else if eq(sgn, t) {
    Nil // csign thinks a - b isn't real
  } else if compar__in(sgn, [q_d_neg, q_d_zero, q_d_nz]) {
    Nil
  } else {
    mk(q_mgreaterp, [a, Fix(0L)])
  }
}

///|
fn mgrp(a : Value, b : Value) -> Value raise {
  if stringp(a) || stringp(b) {
    match (a, b) {
      (Str(sa), Str(sb)) => lbool(string_compare(sb, sa) < 0)
      _ =>
        if symval(q_d_prederror).truthy() {
          merr(
            "greater than: arguments are incomparable; found: ~:M, ~:M",
            [a, b],
          )
        } else {
          Nil
        }
    }
  } else {
    mgrp_general(a, b)
  }
}

///|
fn mlsp(x : Value, y : Value) -> Value raise {
  mgrp(y, x)
}

///|
/// MGQP-GENERAL applies when sign of A - B (possibly complex) makes sense.
fn mgqp_general(a : Value, b : Value) -> Value raise {
  let a = sub(a, b)
  let sgn = csign(a)
  if compar__in(sgn, [q_d_pos, q_d_zero, q_d_pz]) {
    t
  } else if eq(sgn, t) {
    Nil // csign thinks a - b isn't real
  } else if eq(sgn, q_d_neg) {
    Nil
  } else {
    mk(q_mgeqp, [a, Fix(0L)])
  }
}

///|
fn mgqp(a : Value, b : Value) -> Value raise {
  if stringp(a) || stringp(b) {
    match (a, b) {
      (Str(sa), Str(sb)) => lbool(string_compare(sb, sa) <= 0)
      _ =>
        if symval(q_d_prederror).truthy() {
          merr(
            "greater than or equal: arguments are incomparable; found: ~:M, ~:M",
            [a, b],
          )
        } else {
          Nil
        }
    }
  } else {
    mgqp_general(a, b)
  }
}

///|
fn mnqp(x : Value, y : Value, csign? : Value = t) -> Value raise {
  let b = meqp(x, y, csign~)
  if eq(b, q_d_unknown) {
    b
  } else if eq(b, t) || b is Nil {
    lbool(b is Nil)
  } else {
    mk(q_d_notequal, [x, y])
  }
}

///|
fn c__dolpn(o : Value, e : Value) -> Value raise {
  list2(list1(q_mnot), c__dolzero(o, e))
}

///|
fn c__dolzero(o : Value, e : Value) -> Value raise {
  list3(list1(q_d_equal), lmul(nconc(o, e)), Fix(0L))
}

///|
fn c__dolpos(o : Value, e : Value) -> Value raise {
  if o is Nil {
    list2(list1(q_mnot), list3(list1(q_d_equal), lmul(e), Fix(0L)))
  } else if e is Nil {
    list3(list1(q_mgreaterp), lmul(o), Fix(0L))
  } else {
    let e = mapcar(l => power(l, Fix(2L)), e)
    list3(list1(q_mgreaterp), lmul(nconc(o, e)), Fix(0L))
  }
}

///|
fn c__dolpz(o : Value, e : Value) -> Value raise {
  if o is Nil {
    list2(list1(q_mnot), list3(list1(q_d_equal), lmul(e), Fix(0L)))
  } else if e is Nil {
    list3(list1(q_mgeqp), lmul(o), Fix(0L))
  } else {
    let e = mapcar(l => power(l, Fix(2L)), e)
    list3(list1(q_mgeqp), lmul(nconc(o, e)), Fix(0L))
  }
}

///|
fn sign_star(x : Value) -> Value raise {
  compar__with_signs(() => sign1(x))
}

///|
fn infsimp_star(e : Value) -> Value raise {
  if d_mapatom(e).truthy() ||
    (free(e, q_d_inf).truthy() && free(e, q_d_minf).truthy()) {
    e
  } else {
    infsimp(e)
  }
}

///|
/// Maxima sign of a double-float x: $zero, $pos, $neg, or $und (for NaN).
fn sign_float(x : Value) -> Value raise {
  match x {
    Flo(d) if d != d => return q_d_und // NaN check
    _ => ()
  }
  if zerop(x) {
    q_d_zero // ignores signed zero
  } else if minusp(x) {
    q_d_neg
  } else if plusp(x) {
    q_d_pos
  } else {
    merr("sign-float called on ~M ~%", [x])
  }
}

///|
/// `(complex-number-p u #'floatp)`: is U a complex number whose real and
/// imaginary parts are floats? Returns (is-complex, re, im).
fn compar__complex_float_p(u : Value) -> (Bool, Value, Value) raise {
  // With FLOATP as the predicate, the bare %i case (N 1) never applies.
  let mut r : Value = Fix(0L)
  let mut i : Value = Fix(0L)
  if floatp(u) {
    return (true, u, Fix(0L))
  }
  if atom(u) {
    return (false, Nil, Nil)
  }
  if mplusp(u).truthy() {
    if cdddr(u) is Nil && floatp(cadr(u)) {
      r = cadr(u)
      let a2 = caddr(u)
      if mtimesp(a2).truthy() &&
        cdddr(a2) is Nil &&
        floatp(cadr(a2)) &&
        eq(caddr(a2), q_d__pcti) {
        i = cadr(a2)
        return (true, r, i)
      }
    }
    return (false, Nil, Nil)
  }
  if mtimesp(u).truthy() {
    if cdddr(u) is Nil && floatp(cadr(u)) && eq(caddr(u), q_d__pcti) {
      i = cadr(u)
      return (true, r, i)
    }
  }
  (false, Nil, Nil)
}

///|
fn sign_complex_float(x : Value) -> Value raise {
  let (is_complex, re, im) = compar__complex_float_p(x)
  if is_complex { // including the pure real case too
    if zerop(im) {
      sign_float(re) // imaginary part is zero: sign of real part
    } else if compar__cs() && zerop(re) {
      q_d_imaginary
    } else if compar__cs() {
      q_d_complex
    } else {
      imag_err(x)
    }
  } else {
    Nil
  }
}

///|
fn sign1(x : Value) -> Value raise {
  // RISPLIT binds $DOMAIN to '$COMPLEX for its simplifications, but the
  // signs asked for there are those of real values, under the domain outside.
  let rd = symval(q_ear_risplit_domain)
  let dom = if rd.truthy() { rd } else { symval(q_d_domain) }
  with_special(q_d_domain, dom, fn() {
    let x = specrepcheck(x)
    let x = infsimp_star(x)
    let sgn = sign_complex_float(x)
    if sgn.truthy() {
      set(q_sign, sgn) |> ignore
      return sgn
    }
    if compar__cs() && atom(x) && eq(x, q_d_infinity) {
      // In Complex Mode the sign of infinity is complex.
      if symval(q_ear_debug_compar).truthy() {
        format(t, "~& in sign1 detect $infinity.~%", []) |> ignore
      }
      return q_d_complex
    }
    if compar__in(x, [q_d_und, q_d_ind, q_d_infinity]) {
      if !symval(q_limitp).truthy() {
        merr("sign: sign of ~:M is undefined.", [x]) |> ignore
      }
    }
    let mut dum = constp(x)
    let mut exp = x
    if numberp(x) || ratnump(x).truthy() {
      ()
    } else if eq(dum, q_bigfloat) {
      dum = d_bfloat(x)
      if d_bfloatp(dum).truthy() {
        exp = dum
      }
    } else if eq(dum, q_float) {
      dum = numer(x)
      if dum.truthy() && numberp(dum) {
        exp = dum
      }
    } else if (eq(dum, q_numer) || eq(dum, q_symbol)) &&
      {
        dum = numer(x)
        dum is Nil ||
        (numberp(dum) &&
        {
          exp = dum
          num_lt(num_abs(dum), Flo(1.0e-6))
        })
      } {
      if symval(q_d_signbfloat).truthy() {
        dum = d_bfloat(x)
        if dum.truthy() && d_bfloatp(dum).truthy() {
          exp = dum
        }
      } else {
        compar__set4(q_d_pnz, Nil, list1(x), Nil)
        return compar__sign()
      }
    }
    let done = !atom(x) &&
      !mnump(x).truthy() &&
      equal(x, exp) &&
      with_special(q_ear_compsplt_for_sign, t, fn() {
        let (lhs, rhs) = compsplt(x)
        dcompare(lhs, rhs) |> ignore
        let sg = compar__sign()
        if eq(sg, q_d_pos) || eq(sg, q_d_neg) {
          true
        } else if eq(sg, q_d_pnz) {
          false
        } else {
          let s = sg
          let o = symval(q_odds)
          let e = symval(q_evens)
          let m = symval(q_minus)
          sign(x) |> ignore
          if !strongp(compar__sign(), s).truthy() {
            if eq(compar__sign(), q_d_pnz) && eq(s, q_d_pn) {
              set(q_sign, s) |> ignore
            } else {
              compar__set4(s, m, o, e)
            }
          }
          true
        }
      })
    if !done {
      sign(exp) |> ignore
    }
    compar__sign()
  })
}

///|
fn numer(x : Value) -> Value raise {
  // $numer currently has no effect on $float, but is proposed to.
  with_specials([(q_d_numer, t), (q_d_ratprint, Nil)], fn() {
    // Catch a Lisp error, if a floating point overflow occurs.
    let result = with_special(q_errset, Nil, () => errset(() => d_float(x)))
    match result {
      Some(v) => v
      None => Nil
    }
  })
}

///|
fn constp(x : Value) -> Value raise {
  if floatp(x) {
    q_float
  } else if numberp(x) {
    q_numer
  } else if symbolp(x) {
    if compar__in(x, [q_d__pctpi, q_d__pcte, q_d__pctphi, q_d__pctgamma, q_d__pctcatalan]) {
      q_symbol
    } else {
      Nil
    }
  } else if atom(x) {
    Nil
  } else if eq(caar(x), q_rat) {
    q_numer
  } else if eq(caar(x), q_bigfloat) {
    q_bigfloat
  } else if specrepp(x).truthy() {
    constp(specdisrep(x))
  } else {
    let mut ans = q_numer
    for y in cdr(x).iter() {
      let dum = constp(y)
      if eq(dum, q_float) {
        return q_float
      } else if eq(dum, q_numer) {
        ()
      } else if eq(dum, q_bigfloat) {
        ans = q_bigfloat
      } else if eq(dum, q_symbol) {
        if eq(ans, q_numer) {
          ans = q_symbol
        }
      } else {
        return Nil
      }
    }
    ans
  }
}

///|
/// The sign of f-C for a function f whose values lie in RANGE (see the
/// REAL-RANGE property), or NIL when the range does not decide it.
fn sign_from_range(range : Value, c : Value) -> Value raise {
  let lo = car(range)
  let hi = cadr(range)
  if lo.truthy() {
    let s = sign_star(sub(c, car(lo)))
    let r = if eq(s, q_d_neg) {
      q_d_pos
    } else if eq(s, q_d_zero) || eq(s, q_d_nz) {
      if cadr(lo).truthy() {
        q_d_pz
      } else {
        q_d_pos
      }
    } else {
      Nil
    }
    if r.truthy() {
      return r
    }
  }
  if hi.truthy() {
    let s = sign_star(sub(c, car(hi)))
    if eq(s, q_d_pos) {
      q_d_neg
    } else if eq(s, q_d_zero) || eq(s, q_d_pz) {
      if cadr(hi).truthy() {
        q_d_nz
      } else {
        q_d_neg
      }
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// The REAL-RANGE of E when E calls a function with that property and the
/// range applies: carg is real for every argument, the others for real ones.
fn real_range_of(e : Value) -> Value raise {
  let range : Value = if atom(e) { Nil } else { get(caar(e), q_real_range) }
  if range.truthy() &&
    (
      eq(caar(e), q_p_carg) ||
      every(a => zerop1(d_imagpart(a)).truthy(), cdr(e))
    ) {
    range
  } else {
    Nil
  }
}

///|
/// If each term of the sum X is a real constant or a number times a call with
/// a REAL-RANGE, and the bounds these give the sum decide its sign, set SIGN
/// and return T, as SIGNSUM does. Otherwise return NIL.
fn sign_from_sum_range(x : Value) -> Value raise {
  let mut lo : Value = Fix(0L)
  let mut lo_incl : Value = t
  let mut hi : Value = Fix(0L)
  let mut hi_incl : Value = t
  let mut ranged = false
  for term in cdr(x).iter() {
    let k = if mtimesp(term).truthy() &&
      mnump(cadr(term)).truthy() &&
      cdddr(term) is Nil {
      cadr(term)
    } else {
      Fix(1L)
    }
    let range = real_range_of(if eql(k, Fix(1L)) { term } else { caddr(term) })
    if range.truthy() {
      // A negative factor swaps the ends of the range.
      let rr = if mnegp(k).truthy() { reverse(range) } else { range }
      let tlo = car(rr)
      let thi = cadr(rr)
      ranged = true
      lo = if lo.truthy() && tlo.truthy() {
        add2(lo, mul2(k, car(tlo)))
      } else {
        Nil
      }
      lo_incl = if lo_incl.truthy() { cadr(tlo) } else { Nil }
      hi = if hi.truthy() && thi.truthy() {
        add2(hi, mul2(k, car(thi)))
      } else {
        Nil
      }
      hi_incl = if hi_incl.truthy() { cadr(thi) } else { Nil }
    } else if constp(term).truthy() && zerop1(d_imagpart(term)).truthy() {
      lo = if lo.truthy() { add2(lo, term) } else { Nil }
      hi = if hi.truthy() { add2(hi, term) } else { Nil }
    } else {
      return Nil
    }
  }
  let s : Value = if !ranged {
    Nil
  } else {
    let s1 = if lo.truthy() {
      let sl = sign_star(lo)
      if eq(sl, q_d_pos) {
        q_d_pos
      } else if eq(sl, q_d_zero) {
        if lo_incl.truthy() {
          q_d_pz
        } else {
          q_d_pos
        }
      } else {
        Nil
      }
    } else {
      Nil
    }
    if s1.truthy() {
      s1
    } else if hi.truthy() {
      let sh = sign_star(hi)
      if eq(sh, q_d_neg) {
        q_d_neg
      } else if eq(sh, q_d_zero) {
        if hi_incl.truthy() {
          q_d_nz
        } else {
          q_d_neg
        }
      } else {
        Nil
      }
    } else {
      Nil
    }
  }
  if s.truthy() {
    compar__set4(s, Nil, list1(x), Nil)
    t
  } else {
    Nil
  }
}

///|
fn sign(x : Value) -> Value raise {
  if mnump(x).truthy() {
    compar__set4(rgrp(x, Fix(0L)), Nil, Nil, Nil)
    Nil
  } else if compar__cs() && symbolp(x) && eq(x, q_d__pcti) {
    // In Complex Mode the sign of %i is $imaginary.
    set(q_sign, q_d_imaginary)
  } else if symbolp(x) {
    if eq(x, q_d__pcti) {
      imag_err(x) |> ignore
    }
    sign_any(x)
  } else if atom(x) {
    // Numbers and symbols are the only atoms for which sign is defined.
    merr("sign: sign undefined for ~M", [x])
  } else if specrepp(x).truthy() {
    sign(specdisrep(x))
  } else if symbolp(caar(x)) && get(caar(x), q_sign_function).truthy() {
    funcall(get(caar(x), q_sign_function), [x])
  } else if d_subvarp(mop(x)).truthy() &&
    get(mop(mop(x)), q_sign_function).truthy() {
    funcall(get(mop(mop(x)), q_sign_function), [x])
  } else {
    let kind = kind_any_of(caar(x), list2(q_d_posfun, q_d_oddfun))
    if eq(kind, q_d_posfun) {
      sign_posfun(x)
    } else if eq(kind, q_d_oddfun) {
      sign_oddfun(x)
    } else {
      sign_any(x)
    }
  }
}

///|
let compar__lit_assume_pos_pred : Value = list2(
  list1(q_d_assume_pos_pred),
  q_ear_x,
)

///|
fn sign_any(x : Value) -> Value raise {
  // Is X a symbol or a (subscripted) function declared complex or imaginary?
  // DECL-COMPLEX-KIND returns the strongest type, NIL for non-symbols.
  let complex_kind = decl_complex_kind(
    if atom(x) {
      x
    } else if mqapplyp(x).truthy() {
      subfunname(x)
    } else {
      caar(x)
    },
  )
  if eq(complex_kind, q_d_imaginary) {
    if compar__cs() {
      set(q_sign, q_d_imaginary)
    } else {
      // In non-complex mode, imaginary -> error.
      imag_err(x)
    }
  } else if compar__cs() && eq(complex_kind, q_d_complex) {
    set(q_sign, q_d_complex)
  } else {
    dcompare(x, Fix(0L)) |> ignore
    if symval(q_d_assume_pos).truthy() &&
      compar__in(compar__sign(), [q_d_pnz, q_d_pz, q_d_pn]) &&
      (
        if symval(q_d_assume_pos_pred).truthy() {
          with_special(q_ear_x, x, () => is_(compar__lit_assume_pos_pred))
        } else {
          mapatom(x)
        }
      ).truthy() {
      set(q_sign, q_d_pos) |> ignore
    }
    set(q_minus, Nil) |> ignore
    set(q_evens, Nil) |> ignore
    set(
      q_odds,
      if !compar__in(compar__sign(), [q_d_pos, q_d_neg, q_d_zero]) {
        list1(x)
      } else {
        Nil
      },
    )
  }
}

///|
fn sign_mtimes(x : Value) -> Value raise {
  let mut x = cdr(x)
  let mut s = q_d_pos
  let mut m : Value = Nil
  let mut o : Value = Nil
  let mut e : Value = Nil
  while x.truthy() {
    sign1(car(x)) |> ignore
    let sg = compar__sign()
    if eq(sg, q_d_zero) {
      return t
    } else if compar__cs() && eq(sg, q_d_complex) {
      // Found a complex factor. Don't return immediately because another
      // factor could be zero.
      s = q_d_complex
    } else if compar__cs() && eq(s, q_d_complex) {
      () // continue the loop
    } else if compar__cs() && eq(sg, q_d_imaginary) {
      // Found an imaginary factor. Look if we have already one.
      if eq(s, q_d_imaginary) {
        // imaginary*imaginary is real, but of unknown sign.
        s = q_d_pnz
      } else {
        s = sg
      }
    } else if compar__cs() && eq(s, q_d_imaginary) {
      () // continue the loop
    } else if eq(sg, q_d_pos) {
      ()
    } else if eq(sg, q_d_neg) {
      s = flip(s)
      m = lbool(m is Nil)
    } else {
      m = lbool(!eq(m, symval(q_minus)))
      o = nconc(symval(q_odds), o)
      e = nconc(symval(q_evens), e)
      if eq(s, sg) {
        if eq(s, q_d_nz) {
          s = q_d_pz
        }
      } else if eq(s, q_d_pos) {
        s = sg
      } else if eq(s, q_d_neg) {
        s = flip(sg)
      } else if (eq(s, q_d_pz) && eq(sg, q_d_nz)) ||
        (eq(s, q_d_nz) && eq(sg, q_d_pz)) {
        s = q_d_nz
      } else {
        s = q_d_pnz
      }
    }
    x = cdr(x)
  }
  sign_mtimes_finish(s, m, o, e)
}

///|
/// `(remove item l :test test :count 1)` with `(funcall test item elem)`.
fn compar__remove1(
  item : Value,
  l : Value,
  pred : (Value, Value) -> Bool raise,
) -> Value raise {
  let c = Collector::new()
  let mut p = l
  while p is Cons(cell) {
    if pred(item, cell.car) {
      c.append_list(cell.cdr)
      return c.result()
    }
    c.add(cell.car)
    p = cell.cdr
  }
  c.result()
}

///|
/// Store the sign of a product, from the accumulators of SIGN-MTIMES. Two
/// ALIKE1 members of O, the factors of unknown sign, combine to a square and
/// belong in E, so do a member and its negative, with the sign flipped. With
/// nothing left in O, the product is a square times a known sign.
fn sign_mtimes_finish(s : Value, m : Value, o : Value, e : Value) -> Value raise {
  let mut s = s
  let mut m = m
  let mut o = o
  let mut e = e
  if compar__in(s, [q_d_pnz, q_d_pz, q_d_nz, q_d_pn]) {
    let rest = []
    let alike = (u : Value, w : Value) => alike1(u, w).truthy()
    while o.truthy() {
      let a = car(o)
      o = cdr(o)
      if member_if_test(a, o, alike).truthy() {
        o = compar__remove1(a, o, alike)
        e = cons(a, e)
      } else if member_if_test(a, o, (u, w) => alike1(neg(u), w).truthy()).truthy() {
        o = compar__remove1(neg(a), o, alike)
        m = lbool(m is Nil)
        e = cons(a, e)
      } else {
        rest.push(a)
      }
    }
    o = list(rest)
    if o is Nil && e.truthy() {
      let base = if eq(s, q_d_pn) { q_d_pos } else { q_d_pz }
      s = if m.truthy() { flip(base) } else { base }
    }
  }
  compar__set4(s, m, o, e)
  e
}

///|
fn sign_mplus(x : Value) -> Value raise {
  let r = signdiff(x)
  if r.truthy() {
    return r
  }
  let mut s = compar__sign()
  let mut e = symval(q_evens)
  let mut o = symval(q_odds)
  let mut m = symval(q_minus)
  let r = signsum(x)
  if r.truthy() {
    return r
  }
  let r = sign_from_sum_range(x)
  if r.truthy() {
    return r
  }
  if !strongp(s, compar__sign()).truthy() {
    s = compar__sign()
    e = symval(q_evens)
    o = symval(q_odds)
    m = symval(q_minus)
  }
  if !symval(q_factored).truthy() {
    let r = signfactor(x)
    if r.truthy() {
      return r
    }
  }
  let r = strongp(compar__sign(), s)
  if r.truthy() {
    return r
  }
  set(q_sign, s) |> ignore
  set(q_evens, e) |> ignore
  set(q_odds, o) |> ignore
  set(q_minus, m)
}

///|
fn signdiff(x : Value) -> Value raise {
  set(q_sign, q_d_pnz) |> ignore
  let mut swapped = false
  let (l0, r0) = compsplt(x)
  let mut lhs = l0
  let mut rhs = r0
  if mplusp(lhs).truthy() && equal(rhs, Fix(0L)) && cdddr(lhs) is Nil {
    if negp(cadr(lhs)).truthy() && !negp(caddr(lhs)).truthy() {
      rhs = neg(cadr(lhs))
      lhs = caddr(lhs)
    } else if negp(caddr(lhs)).truthy() && !negp(cadr(lhs)).truthy() {
      // Handle a+(-b) by swapping lhs and rhs and flipping the answer
      // (SourceForge bug #3148).
      rhs = cadr(lhs)
      lhs = neg(caddr(lhs))
      swapped = true
    }
  }
  let retval : Value = if equal(rhs, Fix(0L)) || mplusp(lhs).truthy() {
    Nil
  } else {
    if !mnump(rhs).truthy() && compar__in(constp(rhs), [q_numer, q_symbol]) {
      let dum = numer(rhs)
      if numberp(dum) {
        rhs = dum
      }
    }
    if mplusp(rhs).truthy() {
      Nil
    } else {
      let d = dcompare(lhs, rhs)
      let mm = if d.truthy() {
        memq(compar__sign(), list([q_d_pos, q_d_neg, q_d_zero]))
      } else {
        Nil
      }
      if mm.truthy() {
        mm
      } else if !atom(lhs) &&
        !atom(rhs) &&
        eq(caar(lhs), caar(rhs)) &&
        kindp(caar(lhs), q_d_increasing).truthy() {
        sign(sub(cadr(lhs), cadr(rhs))) |> ignore
        t
      } else if !atom(lhs) &&
        !atom(rhs) &&
        eq(caar(lhs), caar(rhs)) &&
        kindp(caar(lhs), q_d_decreasing).truthy() {
        sign(sub(cadr(rhs), cadr(lhs))) |> ignore
        t
      } else if !atom(lhs) &&
        eq(caar(lhs), q_mabs) &&
        alike1(cadr(lhs), rhs).truthy() {
        compar__set4(q_d_pz, Nil, Nil, Nil)
        t
      } else {
        signdiff_special(lhs, rhs)
      }
    }
  }
  // ODDS, EVENS and MINUS describe the swapped difference, so MINUS flips
  // with SIGN.
  if swapped {
    set(q_sign, flip(compar__sign())) |> ignore
    set(q_minus, lbool(symval(q_minus) is Nil)) |> ignore
  }
  // The MABS clause above and SIGNDIFF-SPECIAL blank odds/evens on a weak
  // sign; restore the whole expression so the question refers to X.
  if retval.truthy() &&
    symval(q_odds) is Nil &&
    compar__in(compar__sign(), [q_d_pz, q_d_nz, q_d_pn, q_d_pnz]) {
    set(q_odds, list1(x)) |> ignore
    set(q_evens, Nil) |> ignore
    set(q_minus, Nil) |> ignore
  }
  retval
}

///|
/// If EXPR is a power of base Q (or EXPR = Q, exponent 1), returns the
/// exponent. Otherwise returns NIL. Equality is checked via MEQP.
fn expt_of_base(expr : Value, q : Value) -> Value raise {
  with_specials([(q_d_ratprint, Nil), (q_ear_in_expt_of_base, t)], fn() {
    if mexptp(expr).truthy() {
      if eq(t, meqp(cadr(expr), q)) {
        caddr(expr)
      } else {
        Nil
      }
    } else if eq(t, meqp(expr, q)) {
      Fix(1L)
    } else {
      Nil
    }
  })
}

///|
fn compar__ranged_p(e : Value) -> Bool {
  !atom(e) && (get(caar(e), q_real_range).truthy() || eq(caar(e), q_mabs))
}

///|
fn signdiff_special(xlhs : Value, xrhs : Value) -> Value raise {
  // xlhs may be a constant
  let mut xlhs = xlhs
  let mut xrhs = xrhs
  let mut sgn : Value = Nil
  let mut flip_sign = false
  let c1 = realp(xrhs) &&
    minusp(xrhs) &&
    !atom(xlhs) &&
    eq(sign_star(xlhs), q_d_pos) // e.g. sign(a^3+%pi-1) where a>0
  let c2 = !c1 &&
    mexptp(xlhs).truthy() &&
    // e.g. sign(%e^x-1) where x>0
    eq(sign_star(caddr(xlhs)), q_d_pos) &&
    (
      (
        // Q^Rpos - S, S<=1, Q>1
        compar__in(sign_star(sub(Fix(1L), xrhs)), [q_d_pos, q_d_zero, q_d_pz]) &&
        eq(sign_star(sub(cadr(xlhs), Fix(1L))), q_d_pos)
      ) ||
      (
        !eq(symval(q_d_domain), q_d_complex) &&
        // Qpos ^ Rpos - Spos => Qpos - Spos^(1/Rpos).
        eq(sign_star(cadr(xlhs)), q_d_pos) &&
        eq(sign_star(xrhs), q_d_pos) &&
        // Not when Spos is itself a power of Qpos: that would toggle the
        // exponent R <-> 1/R forever.
        !symval(q_ear_in_expt_of_base).truthy() &&
        !expt_of_base(xrhs, cadr(xlhs)).truthy() &&
        !some(
          p => alike1(car(p), xlhs).truthy() && alike1(cdr(p), xrhs).truthy(),
          symval(q_ear_root_rewrites),
        ) &&
        {
          let xl = xlhs
          let xr = xrhs
          eq(
            with_special(
              q_ear_root_rewrites,
              cons(cons(xl, xr), symval(q_ear_root_rewrites)),
              () => sign_star(
                sub(cadr(xl), power(xr, div(Fix(1L), caddr(xl)))),
              ),
            ),
            q_d_pos,
          )
        }
      )
    )
  let c3 = !c1 &&
    !c2 &&
    mexptp(xlhs).truthy() &&
    mexptp(xrhs).truthy() &&
    // Q^R - Q^T, Q>1, (R-T) > 0, with real R and T
    alike1(cadr(xlhs), cadr(xrhs)).truthy() &&
    zerop1(d_imagpart(caddr(xlhs))).truthy() &&
    zerop1(d_imagpart(caddr(xrhs))).truthy() &&
    eq(sign_star(sub(cadr(xlhs), Fix(1L))), q_d_pos) &&
    eq(sign_star(sub(caddr(xlhs), caddr(xrhs))), q_d_pos)
  if c1 || c2 || c3 {
    sgn = q_d_pos
  }

  // Swap XLHS and XRHS, if necessary, so that XLHS is the function with a
  // known range, or the abs, and remember to flip the result.
  if sgn is Nil && compar__ranged_p(xrhs) && !compar__ranged_p(xlhs) {
    let tmp = xlhs
    xlhs = xrhs
    xrhs = tmp
    flip_sign = !flip_sign
  }

  // sign(f(x) - c) for a function f whose REAL-RANGE gives its bounds.
  let range = if sgn is Nil { real_range_of(xlhs) } else { Nil }
  if range.truthy() {
    sgn = sign_from_range(range, xrhs)
  }

  // signum takes no value strictly between -1 and 1 but 0.
  if sgn is Nil &&
    !atom(xlhs) &&
    eq(caar(xlhs), q_p_signum) &&
    zerop1(d_imagpart(cadr(xlhs))).truthy() &&
    eq(sign_star(add2(xrhs, Fix(1L))), q_d_pos) &&
    eq(sign_star(sub(Fix(1L), xrhs)), q_d_pos) &&
    compar__in(sign_star(xrhs), [q_d_pos, q_d_neg, q_d_pn]) {
    sgn = q_d_pn
  }

  // sign(abs(a) - b) = sign_max(sign(a - b), sign(-a - b)) with real a, b
  if sgn is Nil &&
    !atom(xlhs) &&
    eq(caar(xlhs), q_mabs) &&
    zerop1(d_imagpart(cadr(xlhs))).truthy() &&
    zerop1(d_imagpart(xrhs)).truthy() {
    let a = cadr(xlhs)
    let b = xrhs
    let s1 = sign_star(sub(a, b))
    let s2 = sign_star(sub(neg(a), b))
    let max_sign = sminmax(q_d_max, s1, s2)
    // abs(a) - b >= -b, which the signs of a - b and -a - b need not show.
    if eq(sign_star(neg(b)), q_d_pos) {
      sgn = q_d_pos
    } else if !eq(max_sign, q_d_pnz) {
      sgn = max_sign
    }
  }

  // Swap so that XRHS is the number, e.g. x^2 - 3 -> 3 - x^2.
  if sgn is Nil && mnump(xlhs).truthy() && !mnump(xrhs).truthy() {
    let tmp = xlhs
    xlhs = xrhs
    xrhs = tmp
    flip_sign = !flip_sign
  }

  // sign(a^pos_int - b) = sign((if evenp(pos_int) then abs(a) else a) -
  // b^(1/pos_int)) with real a, real b (>= 0 for even pos_int).
  if sgn is Nil &&
    mnump(xrhs).truthy() &&
    mexptp(xlhs).truthy() &&
    integerp(caddr(xlhs)) &&
    num_gt(caddr(xlhs), Fix(0L)) &&
    (oddp(caddr(xlhs)) || !mnegp(xrhs).truthy()) &&
    zerop1(d_imagpart(cadr(xlhs))).truthy() {
    let exponent = caddr(xlhs)
    let root = mul2(
      if mnegp(xrhs).truthy() {
        Fix(-1L)
      } else {
        Fix(1L)
      },
      power(ftake(q_mabs, [xrhs]), div(Fix(1L), exponent)),
    )
    let base = cadr(xlhs)
    let maybe_abs_base = if evenp(exponent) {
      ftake(q_mabs, [base])
    } else {
      base
    }
    let diff_sign = sign_star(sub(maybe_abs_base, root))
    if !eq(diff_sign, q_d_pnz) {
      sgn = diff_sign
    }
  }

  // sign(Q^m - Q^n) for Q > 0 and real m, n, treating a bare base B as B^1:
  // Q > 1 => sign(m - n), 0 < Q < 1 => sign(n - m).
  if sgn is Nil && !symval(q_ear_in_expt_of_base).truthy() {
    let q = if mexptp(xlhs).truthy() {
      cadr(xlhs)
    } else if mexptp(xrhs).truthy() {
      cadr(xrhs)
    } else {
      Nil
    }
    if q.truthy() {
      // Compare Q with 1 first, as each EXPT-OF-BASE costs an expensive MEQP.
      let qcmp = if eq(sign_star(q), q_d_pos) {
        sign_star(sub(q, Fix(1L)))
      } else {
        Nil
      }
      if eq(qcmp, q_d_pos) || eq(qcmp, q_d_neg) {
        let m = expt_of_base(xlhs, q)
        let n = expt_of_base(xrhs, q)
        if m.truthy() &&
          n.truthy() &&
          zerop1(d_imagpart(m)).truthy() &&
          zerop1(d_imagpart(n)).truthy() {
          let diff_sign = if eq(qcmp, q_d_pos) {
            sign_star(sub(m, n))
          } else {
            sign_star(sub(n, m))
          }
          if !eq(diff_sign, q_d_pnz) {
            sgn = diff_sign
          }
        }
      }
    }
  }
  if sgn is Nil &&
    symval(q_d_useminmax).truthy() &&
    (minmaxp(xlhs).truthy() || minmaxp(xrhs).truthy()) {
    sgn = signdiff_minmax(xlhs, xrhs)
  }
  if sgn.truthy() {
    compar__set4(if flip_sign { flip(sgn) } else { sgn }, Nil, Nil, Nil)
    t
  } else {
    Nil
  }
}

///|
/// Look for symbols with an assumption a > n or a < -n, where n is a number,
/// and shift the symbol a -> a+n in a summation and multiplication. This
/// handles cases like a>1 and b>1 gives sign(a+b-2) -> pos.
fn sign_shift(expr : Value) -> Value raise {
  let mut acc : Value = Nil
  for l in cdr(expr).iter() {
    if symbolp(l) {
      // The facts related to the symbol, newest first.
      let fl = reverse(cdr(facts1(l)))
      acc = cons(l, acc)
      for f in fl.iter() {
        if eq(caar(f), q_mgreaterp) &&
          mnump(caddr(f)).truthy() &&
          eq(d_sign(caddr(f)), q_d_pos) {
          // The case a > n: add the number to the list of terms.
          acc = cons(caddr(f), acc)
          break
        } else if eq(caar(f), q_mgreaterp) &&
          mnump(cadr(f)).truthy() &&
          eq(d_sign(cadr(f)), q_d_neg) {
          // The case a < -n: add the number to the list of terms.
          acc = cons(cadr(f), acc)
          break
        }
      }
    } else if mtimesp(l).truthy() {
      let mut acctimes : Value = Nil
      let mut flag = false
      // Go through the factors of the multiplication.
      for ll in cdr(l).iter() {
        let mut factor_shifted = false
        if symbolp(ll) {
          let fl = reverse(cdr(facts1(ll)))
          for f in fl.iter() {
            if eq(caar(f), q_mgreaterp) &&
              mnump(caddr(f)).truthy() &&
              eq(d_sign(caddr(f)), q_d_pos) {
              flag = true
              factor_shifted = true
              acctimes = cons(add2(ll, caddr(f)), acctimes)
              break
            } else if eq(caar(f), q_mgreaterp) &&
              mnump(cadr(f)).truthy() &&
              eq(d_sign(cadr(f)), q_d_neg) {
              flag = true
              factor_shifted = true
              acctimes = cons(add2(ll, cadr(f)), acctimes)
              break
            }
          }
          if !factor_shifted {
            acctimes = cons(ll, acctimes)
          }
        } else {
          acctimes = cons(ll, acctimes)
        }
      }
      if flag {
        // If a shift has been done expand the factors.
        acc = cons(d_multthru(muln(acctimes, Nil)), acc)
      } else {
        acc = cons(muln(acctimes, Nil), acc)
      }
    } else {
      acc = cons(l, acc)
    }
  }
  addn(acc, Nil)
}

///|
fn signsum(x : Value) -> Value raise {
  // SIGN-SHIFT rewrites X into an expression of the same sign. ODDS, which
  // ASKSIGN asks about, must name X itself: ORIG is X with the terms found to
  // be zero taken out.
  let mut orig = x
  let mut x = sign_shift(x)
  // x might be simplified to a single term in sign-shift.
  if !mplusp(x).truthy() {
    x = cons(list1(q_mplus), list1(x))
  }
  let mut s = q_d_zero
  for l in cdr(x).iter() {
    // Call sign1 and not sign, because sign1 handles constant expressions.
    sign1(l) |> ignore
    let sg = compar__sign()
    if compar__cs() && eq(sg, q_d_complex) {
      // Found a complex expression. The sign is $complex.
      compar__set4(q_d_complex, Nil, Nil, Nil)
      return t
    } else if compar__cs() && eq(sg, q_d_imaginary) {
      // An imaginary term: zero becomes imaginary, imaginary stays,
      // anything else makes the sum complex.
      if eq(s, q_d_zero) {
        s = q_d_imaginary
      } else if !eq(s, q_d_imaginary) {
        compar__set4(q_d_complex, Nil, Nil, Nil)
        return t
      }
    } else if (
        eq(sg, q_d_zero) &&
        {
          orig = sub(orig, l)
          orig.truthy()
        }
      ) ||
      (eq(s, sg) && !eq(s, q_d_pn)) || // $PN + $PN = $PNZ
      (eq(s, q_d_pos) && eq(sg, q_d_pz)) ||
      (eq(s, q_d_neg) && eq(sg, q_d_nz)) {
      ()
    } else if (
        compar__in(sg, [q_d_pz, q_d_pos]) && compar__in(s, [q_d_zero, q_d_pz])
      ) ||
      (compar__in(sg, [q_d_nz, q_d_neg]) && compar__in(s, [q_d_zero, q_d_nz])) ||
      (eq(sg, q_d_pn) && eq(s, q_d_zero)) {
      s = sg
    } else if compar__cs() && eq(s, q_d_imaginary) {
      // A non-zero real term and an imaginary sum: the total is complex.
      compar__set4(q_d_complex, Nil, Nil, Nil)
      return t
    } else {
      // Carry on with an indeterminate total rather than stop here: a later
      // term may be non-real, and SIGN1 reports that by throwing.
      s = q_d_pnz
    }
  }
  compar__set4(s, Nil, list1(orig), Nil)
  if eq(s, q_d_pnz) {
    Nil
  } else {
    t
  }
}

///|
fn signfactor(x : Value) -> Value raise {
  with_special(q_factored, t, fn() {
    let y0 = factor_linear_sum(x)
    let y = if y0.truthy() { y0 } else { factor_if_small(x) }
    if mplusp(y).truthy() || num_gt(conssize(y), Fix(50L)) {
      set(q_sign, q_d_pnz) |> ignore
      Nil
    } else {
      // SIGN returns nothing useful. Return NIL, so that SIGN-MPLUS keeps the
      // stronger of this sign and the one it had before.
      sign(y) |> ignore
      Nil
    }
  })
}

///|
fn factor_if_small(x : Value) -> Value raise {
  if num_lt(conssize(x), Fix(51L)) {
    with_specials(
      [(q_d_ratprint, Nil), (q_d_factor_max_degree_print_warning, Nil)],
      () => factor(x),
    )
  } else {
    x
  }
}

///|
fn compar__linear_kernel_p(e : Value) -> Bool {
  atom(e) || !compar__in(caar(e), [q_mplus, q_mtimes, q_mexpt])
}

///|
/// For a sum with rational coefficients that is linear in its kernels, pull
/// out the numeric content and make the coefficient of the last term
/// positive, as FACTOR would. Returns X when that changes nothing, and NIL for
/// any other sum. The product stays unsimplified.
fn factor_linear_sum(x : Value) -> Value raise {
  let mut g : Value = Fix(0L)
  let mut l : Value = Fix(1L)
  let mut c : Value = Nil
  for term in cdr(x).iter() {
    c = if mnump(term).truthy() {
      term
    } else if compar__linear_kernel_p(term) {
      Fix(1L)
    } else if mtimesp(term).truthy() &&
      cdddr(term) is Nil &&
      compar__linear_kernel_p(caddr(term)) {
      cadr(term)
    } else {
      Nil
    }
    if !(integerp(c) || ratnump(c).truthy()) {
      return Nil
    }
    g = num_gcd(g, num1(c))
    l = num_lcm(l, denom1(c))
  }
  let g = div(if minusp(num1(c)) { num_neg(g) } else { g }, l)
  if eql(g, Fix(1L)) {
    x
  } else {
    list3(list1(q_mtimes), g, addn(mapcar(e => div(e, g), cdr(x)), t))
  }
}

///|
fn sign_mexpt(x : Value) -> Value raise {
  let expt = caddr(x)
  let base1 = cadr(x)
  let mut sign_expt = sign1(expt)
  let mut sign_base = sign1(base1)
  let mut evod_ = evod(expt)
  let mut expt_num = expt
  let mut even_root = false

  // With domain : real and an odd denominator, base^(num/denom) has the sign
  // of base^num, so use the parity of num instead. An odd num over an even
  // denominator is an even root - not real for a negative base. Only a base
  // that may be negative needs this.
  if evod_ is Nil &&
    !mnump(expt).truthy() &&
    compar__in(sign_base, [q_d_neg, q_d_nz, q_d_pn, q_d_pnz]) {
    let (num, denom) = with_specials(
      [(q_d_exptdispflag, t), (q_d_pfeformat, Nil), (q_d__pctedispflag, Nil)],
      () => num_denom_split(expt),
    )
    if !eql(denom, Fix(1L)) {
      let evod_denom = evod(denom)
      if eq(evod_denom, q_d_odd) && !eq(symval(q_d_domain), q_d_complex) {
        evod_ = evod(num)
        expt_num = num
      } else if eq(evod_denom, q_d_even) {
        even_root = eq(evod(num), q_d_odd)
      }
    }
  }
  let dbg = (msg : String) => if symval(q_ear_debug_compar).truthy() {
    format(t, msg, [x]) |> ignore
  }

  // The variable sign is now equal to sign-base.
  if eq(sign_base, q_d_zero) &&
    compar__in(sign_expt, [q_d_zero, q_d_neg, q_d_nz]) {
    dbzs_err(x) |> ignore
  } else if eq(sign_expt, q_d_zero) {
    set(q_sign, q_d_pos) |> ignore
  } else if eq(sign_base, q_d_zero) {
    ()
  } else if compar__cs() &&
    (
      eq(sign_expt, q_d_complex) ||
      eq(sign_expt, q_d_imaginary) ||
      eq(sign_base, q_d_complex)
    ) {
    // Base is complex or exponent is complex or imaginary.
    dbg("~&in SIGN-MEXPT for ~A, sign is complex.~%")
    set(q_sign, q_d_complex) |> ignore
  } else if compar__cs() &&
    compar__in(sign_base, [q_d_neg, q_d_nz]) &&
    eq(evod(d_expand(mul2(Fix(2L), expt))), q_d_odd) {
    // Base is non-positive and the double of the exponent is odd.
    dbg("~&in SIGN-MEXPT for ~A, sign is $imaginary.~%")
    set(q_sign, q_d_imaginary) |> ignore
  } else if compar__cs() && eq(sign_base, q_d_imaginary) {
    // An imaginary base. Look for even or odd exponent.
    dbg("~&in SIGN-MEXPT for ~A, base is $imaginary.~%")
    if eq(evod_, q_d_even) {
      let evod_half = evod(d_expand(div(expt, Fix(2L))))
      set(
        q_sign,
        if eq(evod_half, q_d_even) {
          q_d_pz
        } else if eq(evod_half, q_d_odd) {
          q_d_nz
        } else {
          q_d_pnz
        },
      )
      |> ignore
    } else if eq(evod_, q_d_odd) {
      set(q_sign, q_d_imaginary) |> ignore
      set(
        q_minus,
        lbool(eq(evod(d_expand(div(sub(expt, Fix(1L)), Fix(2L)))), q_d_odd)),
      )
      |> ignore
    } else {
      set(q_sign, q_d_complex) |> ignore
    }
  } else if compar__cs() &&
    eq(symval(q_d_domain), q_d_complex) &&
    ratnump(expt).truthy() &&
    compar__in(sign_base, [q_d_neg, q_d_nz, q_d_pn, q_d_pnz]) {
    // With domain : complex, a base that might be negative raised to a
    // non-integer rational power is on the principal branch, never real.
    dbg("~&in SIGN-MEXPT for ~A, branch is complex.~%")
    set(q_sign, q_d_complex) |> ignore
  } else if compar__cs() &&
    evod_ is Nil &&
    !ratnump(expt).truthy() &&
    !compar__in(sign_base, [q_d_pos, q_d_pz, q_d_zero]) {
    dbg("~&in SIGN-MEXPT for ~A, base is not $pos, $pz or $zero.~%")
    set(
      q_sign,
      if maxima_integerp(expt_num).truthy() {
        q_d_pnz
      } else {
        q_d_complex
      },
    )
    |> ignore
  } else if even_root {
    // Real mode: an even root of a negative base is an error; otherwise
    // assume the base is not negative.
    if eq(sign_base, q_d_neg) ||
      (eq(sign_base, q_d_nz) && eq(sign_expt, q_d_neg)) {
      imag_err(x) |> ignore
    } else if eq(sign_base, q_d_pn) || eq(sign_expt, q_d_neg) {
      set(q_sign, q_d_pos) |> ignore
    } else if eq(sign_base, q_d_nz) {
      set(q_sign, q_d_zero) |> ignore
    } else {
      set(q_sign, q_d_pz) |> ignore
    }
  } else if eq(sign_base, q_d_pos) {
    ()
  } else if eq(evod_, q_d_even) {
    if eq(sign_expt, q_d_neg) {
      compar__set4(q_d_pos, Nil, Nil, list1(base1))
    } else if compar__in(sign_base, [q_d_pn, q_d_neg]) {
      let ev = nconc(symval(q_odds), symval(q_evens))
      compar__set4(q_d_pos, Nil, Nil, ev)
    } else {
      let ev = nconc(symval(q_odds), symval(q_evens))
      compar__set4(q_d_pz, Nil, Nil, ev)
    }
  } else if eq(evod_, q_d_odd) && compar__in(sign_base, [q_d_neg, q_d_nz]) {
    // An odd power (or odd root) of a non-positive base has the sign of the
    // base. A negative exponent rules out zero.
    if eq(sign_base, q_d_nz) && compar__in(sign_expt, [q_d_neg, q_d_nz]) {
      set(q_sign, q_d_neg) |> ignore
    }
  } else if eq(sign_expt, q_d_neg) &&
    d_ratnump(expt).truthy() &&
    d_evenp(d_denom(expt)).truthy() &&
    compar__in(sign_base, [q_d_pnz, q_d_pos, q_d_pz, q_d_pn]) &&
    (!compar__cs() || compar__in(sign_base, [q_d_pos, q_d_pz])) {
    // (pnz, pos, pz or pn)^(-odd/even) = pos, e.g. sign(1/sqrt(x)) = pos.
    set(q_sign, q_d_pos) |> ignore
  } else if compar__in(sign_expt, [q_d_neg, q_d_nz]) &&
    compar__in(sign_base, [q_d_nz, q_d_pz, q_d_pnz]) &&
    // Leave rational exponents to the (RATNUMP EXPT) clause.
    !ratnump(expt).truthy() {
    compar__set4(
      if eq(sign_base, q_d_pz) {
        q_d_pos
      } else {
        q_d_pn
      },
      Nil,
      list1(x),
      Nil,
    )
  } else if compar__in(sign_expt, [q_d_pz, q_d_nz, q_d_pnz]) {
    if compar__in(sign_base, [q_d_neg, q_d_nz]) {
      compar__set4(
        if eq(sign_base, q_d_neg) {
          q_d_pn
        } else {
          q_d_pnz
        },
        Nil,
        list1(x),
        Nil,
      )
    }
  } else if eq(sign_expt, q_d_pn) {
    if eq(sign_base, q_d_neg) {
      compar__set4(q_d_pn, Nil, list1(x), Nil)
    } else if eq(sign_base, q_d_nz) {
      compar__set4(q_d_pnz, Nil, list1(x), Nil)
    }
  } else if ratnump(expt).truthy() {
    if eq(symval(q_d_domain), q_d_complex) && eq(sign_base, q_d_neg) {
      // With domain : complex, a negative base raised to a non-integer
      // rational power is on the principal branch, never real.
      imag_err(x) |> ignore
    } else if !eq(symval(q_d_domain), q_d_complex) &&
      mevenp(cadr(expt)).truthy() {
      if compar__in(sign_base, [q_d_pn, q_d_neg]) {
        sign_base = q_d_pos
      } else if compar__in(sign_base, [q_d_pnz, q_d_nz]) {
        sign_base = q_d_pz
      }
      let ev = nconc(symval(q_odds), symval(q_evens))
      set(q_evens, ev) |> ignore
      set(q_odds, Nil) |> ignore
      set(q_minus, Nil) |> ignore
    } else if eq(symval(q_d_domain), q_d_complex) ||
      mevenp(caddr(expt)).truthy() {
      // No real value for a negative base.
      if compar__cs() {
        if !compar__in(sign_base, [q_d_pos, q_d_pz]) {
          // In Complex Mode the sign is $complex.
          sign_expt = q_d_complex
          sign_base = q_d_complex
        }
      } else if symval(q_complexsign).truthy() {
        // The only place the variable complexsign is used (to_poly_solve
        // depends on it).
        sign_expt = q_d_pnz
        sign_base = q_d_pnz
      } else if eq(sign_base, q_d_neg) {
        imag_err(x) |> ignore
      } else if eq(sign_base, q_d_pn) {
        sign_base = q_d_pos
      } else if eq(sign_base, q_d_nz) {
        sign_base = q_d_zero
      } else {
        sign_base = q_d_pz
      }
    }
    if eq(sign_expt, q_d_neg) {
      // $ZERO here came from $NZ. A negative exponent rules out zero, leaving
      // a negative base: not real -> error (we're in real mode here).
      if eq(sign_base, q_d_zero) {
        imag_err(x) |> ignore
      } else if eq(sign_base, q_d_pz) {
        sign_base = q_d_pos
      } else if eq(sign_base, q_d_nz) {
        sign_base = q_d_neg
      } else if eq(sign_base, q_d_pnz) {
        sign_base = q_d_pn
      }
    }
    set(q_sign, sign_base) |> ignore
  } else if compar__in(sign_base, [q_d_neg, q_d_nz]) {
    if eq(evod_, q_d_odd) {
      ()
    } else if compar__cs() {
      set(q_sign, q_d_complex) |> ignore
    } else if eq(sign_base, q_d_neg) {
      compar__set4(q_d_pn, Nil, list1(x), Nil)
    } else {
      compar__set4(q_d_pnz, Nil, list1(x), Nil)
    }
  }
  compar__sign()
}

///|
/// Determine the sign of log(expr). This function changes the special
/// variable sign.
fn sign_log(x : Value) -> Value raise {
  let arg = cadr(x)
  sign1(arg) |> ignore // sets SIGN, MINUS, ODDS, EVENS, describing ARG.
  let arg_sign = compar__sign()
  let sg = compar__sign()
  let new_sign = if eq(sg, q_d_zero) {
    log0_err(x) // log(0) is undefined.
  } else if compar__in(sg, [q_d_pos, q_d_pz]) {
    // log(ARG) has the sign of ARG - 1. Where that leaves open whether
    // ARG = 1, ask MEQP, which can decide more cases.
    let s = csign(sub(arg, Fix(1L)))
    if compar__in(s, [q_d_pos, q_d_neg, q_d_zero, q_d_pn]) {
      s
    } else {
      // For a weak sign of ARG - 1, the second try in MEQP can be skipped.
      let one = meqp(
        arg,
        Fix(1L),
        csign=lbool(!compar__in(s, [q_d_pz, q_d_nz, q_d_pnz])),
      )
      if eq(one, t) {
        q_d_zero // log(1) = 0.
      } else if compar__in(s, [q_d_pz, q_d_nz]) {
        s
      } else if one is Nil {
        q_d_pn
      } else {
        q_d_pnz
      }
    }
  } else if compar__cs() && eql(Fix(1L), cabs(arg)) {
    q_d_imaginary
  } else if compar__cs() {
    q_d_complex
  } else if compar__in(sg, [q_d_pnz, q_d_pn]) {
    q_d_pnz
  } else {
    imag_err(x)
  }
  set(q_sign, new_sign) |> ignore
  // If SIGN isn't $POS, $NEG or $ZERO, $ASKSIGN asks for the sign of the
  // expression described by MINUS, ODDS and EVENS: for a nonnegative ARG,
  // that is ARG - 1; where ARG may be negative, log(ARG) itself.
  set(q_minus, Nil) |> ignore
  set(q_evens, Nil) |> ignore
  set(
    q_odds,
    if !compar__in(compar__sign(), [q_d_pos, q_d_neg, q_d_zero]) {
      list1(
        if compar__in(arg_sign, [q_d_pos, q_d_pz]) {
          sub(arg, Fix(1L))
        } else {
          x
        },
      )
    } else {
      Nil
    },
  )
}

///|
fn sign_mabs(x : Value) -> Value raise {
  with_special(q_ear_complexsign, t, fn() {
    sign(cadr(x)) |> ignore
    let sg = compar__sign()
    if compar__in(sg, [q_d_pos, q_d_zero]) {
      ()
    } else if compar__in(sg, [q_d_neg, q_d_pn]) {
      set(q_sign, q_d_pos) |> ignore
    } else if member_if_test(
        cadr(x),
        symval(q_ear_sign_mabs_args),
        (u, w) => alike1(u, w).truthy(),
      )
      is Nil &&
      eq(
        t,
        with_special(
          q_ear_sign_mabs_args,
          cons(cadr(x), symval(q_ear_sign_mabs_args)),
          // abs(nonzero) > 0. If SIGN found nothing ($PNZ), let MNQP skip a
          // redundant second $CSIGN call.
          () => mnqp(Fix(0L), cadr(x), csign=lbool(!eq(compar__sign(), q_d_pnz))),
        ),
      ) {
      set(q_sign, q_d_pos) |> ignore
    } else {
      let ev = nconc(symval(q_odds), symval(q_evens))
      compar__set4(q_d_pz, Nil, Nil, ev)
    }
    compar__sign()
  })
}

///|
fn sign_asin_slacos_slatanh(x : Value) -> Value raise {
  if compar__cs() && eq(caar(x), q_p_acos) && eq(t, mgrp(cadr(x), Fix(1L))) {
    // acos(x) = %i*acosh(x) for x > 1, so it's imaginary. asin and atanh are
    // merely complex off [-1, 1].
    set(q_sign, q_d_imaginary)
  } else if compar__cs() &&
    (
      !eq(t, mgqp(cadr(x), Fix(-1L))) || !eq(t, mgqp(Fix(1L), cadr(x)))
    ) {
    set(q_sign, q_d_complex)
  } else if !compar__cs() &&
    (eq(t, mgrp(cadr(x), Fix(1L))) || eq(t, mlsp(cadr(x), Fix(-1L)))) {
    // Provably off [-1, 1], where none of the three is real.
    imag_err(x)
  } else if !eq(caar(x), q_p_acos) {
    sign_oddfun(x)
  } else if eq(t, mlsp(cadr(x), Fix(1L))) {
    sign_posfun(x)
  } else {
    set(q_sign, q_d_pz) // x <= 1
  }
}

///|
fn sign_acosh(x : Value) -> Value raise {
  if compar__cs() &&
    eq(t, mgqp(cadr(x), Fix(-1L))) &&
    eq(t, mlsp(cadr(x), Fix(1L))) {
    // acosh(x) = %i*acos(x) for -1 <= x < 1, so it's imaginary.
    set(q_sign, q_d_imaginary)
  } else if compar__cs() && !eq(t, mgqp(cadr(x), Fix(1L))) {
    set(q_sign, q_d_complex)
  } else if !compar__cs() && eq(t, mlsp(cadr(x), Fix(1L))) {
    // Provably non-real.
    imag_err(x)
  } else if eq(t, mgrp(cadr(x), Fix(1L))) {
    sign_posfun(x)
  } else {
    set(q_sign, q_d_pz) // x >= 1
  }
}
