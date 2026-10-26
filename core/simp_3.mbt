// Port of src/simp.lisp, part 3: SIMPEXPT and TIMESIN.

///|
priv enum SimpExptLbl {
  Cont
  Opp
  Start
  Retno
  Atgr
  Up
  Matrix
  E1
}

///|
/// `(member s '($pos $pz $zero))`
fn simp__pos_pz_zero_p(s : Value) -> Bool {
  eq(s, q_d_pos) || eq(s, q_d_pz) || eq(s, q_d_zero)
}

///|
/// `(member s '($neg $nz))`
fn simp__neg_nz_p(s : Value) -> Bool {
  eq(s, q_d_neg) || eq(s, q_d_nz)
}

///|
fn simpexpt(x : Value, y : Value, z : Value) -> Value raise {
  let rb = bind(q_ear_rulesw, Nil)
  defer unbind(rb)
  let mut y = y
  let mut z = z
  let check = x
  let mut gr : Value = Nil
  let mut pot : Value = Nil
  let mut res : Value = Nil
  let mut w : Value = Nil
  let mut mlpgr : Value = Nil
  let mut mlppot : Value = Nil
  let mut factor_signs : Value = Nil
  twoargcheck(x) |> ignore
  if z.truthy() {
    gr = cadr(x)
    pot = caddr(x)
  } else {
    gr = simplifya(cadr(x), Nil)
    pot = simplifya(
      if symval(q_d_ratsimpexpons).truthy() {
        d_ratsimp(caddr(x), Nil)
      } else {
        caddr(x)
      },
      Nil,
    )
  }
  let domain_real = () => eq(symval(q_d_domain), q_d_real)
  let domain_complex = () => eq(symval(q_d_domain), q_d_complex)
  let mut lbl = SimpExptLbl::Cont
  while true {
    match lbl {
      Cont => {
        if d_ratp(pot).truthy() {
          pot = ratdisrep(pot)
          continue
        }
        if d_ratp(gr).truthy() {
          if member(q_trunc, car(gr)).truthy() {
            return srf(list3(list1(q_mexpt), gr, pot))
          } else if integerp(pot) {
            let g = gr
            let p = pot
            return with_specials(
              [(q_varlist, caddar(g)), (q_genvar, cadddr(car(g)))],
              () => ratrep_star(list3(list1(q_mexpt), g, p)),
            )
          } else {
            gr = ratdisrep(gr)
            continue
          }
        }
        mlpgr = mxorlistp(gr)
        if mlpgr.truthy() {
          lbl = Matrix
          continue
        }
        mlppot = mxorlistp(pot)
        if mlppot.truthy() {
          lbl = Matrix
          continue
        }
        // Fast-path for a symbolic base other than %i (handled separately):
        if symbolp(gr) && !eq(gr, q_d__pcti) {
          lbl = if zerop1(pot).truthy() { Retno } else { Atgr }
          continue
        }
        if onep1(pot).truthy() {
          lbl = Atgr
          continue
        }
        if zerop1(pot).truthy() || onep1(gr).truthy() {
          lbl = Retno
          continue
        }
        // This code tries to handle 0^a more complete.
        if zerop1(gr).truthy() {
          z = d_csign(pot)
          if simp__neg_nz_p(z) ||
            (
              symval(q_n_starzexptsimp_q).truthy() &&
              eq(d_asksign(pot), q_d_neg)
            ) {
            // A negative exponent. Maxima error.
            return if !symval(q_errorsw).truthy() {
              merr("expt: undefined: 0 to a negative exponent.", [])
            } else {
              throw_tag(q_errorsw, t)
            }
          } else if simp__complex_sign_p(z) &&
            {
              // A complex exponent. Look at the sign of the realpart.
              z = d_sign(d_realpart(pot))
              simp__neg_nz_p(z) || eq(z, q_d_zero)
            } {
            return if !symval(q_errorsw).truthy() {
              merr("expt: undefined: 0 to a complex exponent.", [])
            } else {
              throw_tag(q_errorsw, t)
            }
          } else if symval(q_n_starzexptsimp_q).truthy() &&
            eq(d_asksign(pot), q_d_zero) {
            return if !symval(q_errorsw).truthy() {
              merr("expt: undefined: 0^0", [])
            } else {
              throw_tag(q_errorsw, t)
            }
          } else if !(eq(z, q_d_pos) || eq(z, q_d_pz)) {
            // The sign of realpart(pot) is not known. We return ZERO.
            if !free(pot, q_d__pcti).truthy() {
              return if !symval(q_errorsw).truthy() {
                merr("expt: undefined: 0 to a complex exponent.", [])
              } else {
                throw_tag(q_errorsw, t)
              }
            } else {
              // Return ZERO and not an unsimplified expression.
              return zerores(gr, pot)
            }
          } else {
            return zerores(gr, pot)
          }
        }
        if mnump(gr).truthy() &&
          mnump(pot).truthy() &&
          (!ratnump(gr).truthy() || !ratnump(pot).truthy()) {
          return eqtest(exptrl(gr, pot), check)
        }
        // Check for numerical evaluation of the sqrt.
        if alike1(pot, mk(q_rat, [Fix(1L), Fix(2L)])).truthy() &&
          {
            res = flonum_eval(q_p_sqrt, gr)
            res.truthy() ||
            (
              !member(q_simp, cdar(x)).truthy() &&
              {
                res = big_float_eval(q_p_sqrt, gr)
                res.truthy()
              }
            )
          } {
          return res
        }
        if eq(gr, q_d__pcti) {
          return p_itopot(pot)
        }
        let pot_parity = if realp(gr) && minusp(gr) { evod(pot) } else { Nil }
        if eq(q_d_even, pot_parity) {
          gr = num_neg(gr)
          continue
        }
        if eq(q_d_odd, pot_parity) {
          return mul2(Fix(-1L), power(num_neg(gr), pot))
        }
        if equal(gr, Fix(-1L)) &&
          mminusp(pot).truthy() &&
          maxima_integerp(pot).truthy() {
          pot = neg(pot)
          continue
        }
        if equal(gr, Fix(-1L)) &&
          mtimesp(pot).truthy() &&
          length(pot) == 3 &&
          integerp(cadr(pot)) &&
          oddp(cadr(pot)) &&
          maxima_integerp(pot).truthy() &&
          maxima_integerp(caddr(pot)).truthy() {
          pot = caddr(pot)
          continue
        }
        if atom(gr) {
          lbl = Atgr
          continue
        }
        let abs_ok = () => (
            domain_real() &&
            !apparently_complex_to_judge_by__dolcsign_p(cadr(gr)).truthy()
          ) ||
          (
            domain_complex() &&
            apparently_real_to_judge_by__dolcsign_p(cadr(gr)).truthy()
          )
        if eq(caar(gr), q_mabs) &&
          (
            mevenp(pot).truthy() ||
            // abs(x)^(2*m/n) -> x^(2*m/n) only for the real root of x^(1/n),
            // not for the principal branch (domain : complex).
            (domain_real() && evnump(pot).truthy())
          ) &&
          abs_ok() {
          return power(cadr(gr), pot)
        }
        if eq(caar(gr), q_mabs) &&
          integerp(pot) &&
          oddp(pot) &&
          !equal(pot, Fix(-1L)) &&
          abs_ok() {
          // abs(x)^(2*n+1) -> abs(x)*x^(2*n), n an integer number
          return if plusp(pot) {
            mul2(power(cadr(gr), add2(pot, Fix(-1L))), gr)
          } else {
            mul2(power(cadr(gr), add2(pot, Fix(1L))), inv(gr))
          }
        }
        // signum(real)^int = signum(real)^{-2, -1, 1, 2} or 1, depending on
        // the sign and parity of int, and whether real can be zero.
        if eq(caar(gr), q_p_signum) && integerp(pot) {
          let arg_sign = d_csign(cadr(gr))
          if !simp__complex_sign_p(arg_sign) {
            if eq(arg_sign, q_d_zero) ||
              eq(arg_sign, q_d_pnz) ||
              eq(arg_sign, q_d_pz) ||
              eq(arg_sign, q_d_nz) {
              // real can be zero, so if the exponent is negative, it has to
              // stay negative.
              let new_pot = num_mul(
                signum(pot),
                if evenp(pot) {
                  Fix(2L)
                } else {
                  Fix(1L)
                },
              )
              if num_eq(new_pot, pot) {
                lbl = Up
                continue
              } else {
                return power(gr, new_pot)
              }
            } else {
              // real cannot be zero. Simplify signum(real)^int to 1 for even
              // int and signum(real) for odd int.
              return if evenp(pot) { Fix(1L) } else { gr }
            }
          }
        }
        if eq(caar(gr), q_mequal) {
          return eqtest(
            list3(list1(caar(gr)), power(cadr(gr), pot), power(caddr(gr), pot)),
            gr,
          )
        }
        if symbolp(pot) {
          lbl = Opp
          continue
        }
        if eq(caar(gr), q_mexpt) {
          lbl = E1
          continue
        }
        if eq(caar(gr), q_p_sum) &&
          symval(q_d_sumexpand).truthy() &&
          integerp(pot) &&
          plusp(pot) &&
          num_lt(pot, symval(q_d_maxposex)) {
          let mut i = one_minus(pot)
          let mut an = gr
          while !zerop(i) {
            let an1 = simptimes(list3(list1(q_mtimes), an, gr), Fix(1L), t)
            i = one_minus(i)
            an = an1
          }
          return an
        }
        if equal(pot, Fix(-1L)) {
          return eqtest(
            if !mtimesp(gr).truthy() &&
              eq(get(q_mexpt, q_operators), q_simpexpt) {
              // The MEXPT simplifier is original (no tellsimp).
              // TMS/TIMESIN can only rebuild GR^POT unchanged here.
              list3(list2(q_mexpt, q_simp), gr, pot)
            } else {
              testt(tms(gr, pot, Nil))
            },
            check,
          )
        }
        if fixnump(pot) {
          return eqtest(
            if mplusp(gr).truthy() &&
              !(
                num_gt(pot, symval(q_d_expop)) ||
                num_gt(num_neg(pot), symval(q_d_expon))
              ) {
              expandexpt(gr, pot)
            } else if !mtimesp(gr).truthy() &&
              eq(get(q_mexpt, q_operators), q_simpexpt) &&
              eq(get(q_mtimes, q_operators), q_simptimes) {
              // See comment above.
              list3(list2(q_mexpt, q_simp), gr, pot)
            } else {
              simplifya(tms(gr, pot, Nil), t)
            },
            check,
          )
        }
        lbl = Opp
      }
      Opp => {
        if eq(caar(gr), q_mexpt) {
          lbl = E1
          continue
        }
        if eq(caar(gr), q_rat) {
          return mul2(
            power(cadr(gr), pot),
            power(caddr(gr), mul2(Fix(-1L), pot)),
          )
        }
        if !eq(caar(gr), q_mtimes) {
          lbl = Up
          continue
        }
        let radexpand = symval(q_d_radexpand)
        if eq(radexpand, q_d_all) ||
          (
            radexpand.truthy() &&
            simplexpon(pot).truthy() &&
            // With domain:real an odd root of a negative factor is
            // the real root, which is right only if all factors are
            // real. Leave a product with a factor that may be complex
            // to the $CSIGN loop below, which reuses FACTOR-SIGNS.
            (
              maxima_integerp(pot).truthy() ||
              {
                factor_signs = mapcar(f => d_csign(f), cdr(gr))
                !some(s => simp__complex_sign_p(s), factor_signs)
              }
            )
          ) {
          res = list1(Fix(1L))
          lbl = Start
          continue
        }
        if (!numberp(cadr(gr)) || equal(cadr(gr), Fix(-1L))) &&
          {
            // Only for -1. W gets the denominator.
            let g = gr
            let (num, denom) = with_specials(
              [(q_d_exptdispflag, t), (q_d_pfeformat, Nil), (q_d__pctedispflag, Nil)],
              () => num_denom_split(g),
            )
            equal(Fix(-1L), num) &&
            {
              w = denom
              w.truthy()
            }
          } &&
          // Do not simplify for a complex base.
          !simp__complex_sign_p(d_csign(gr)) &&
          domain_real() &&
          radexpand.truthy() {
          // (-1/x)^a -> 1/(-x)^a for x negative
          // For all other cases (-1)^a/x^a
          return if eq(d_csign(w), q_d_neg) {
            inv(power(neg(w), pot))
          } else {
            div(power(Fix(-1L), pot), power(w, pot))
          }
        }
        if domain_complex() || !radexpand.truthy() {
          lbl = Up
          continue
        }
        let mut l = cdr(gr)
        let mut res : Value = list1(Fix(1L))
        let mut rad : Value = Nil
        let mut signs = factor_signs
        while !(l is Nil) {
          // Check with $csign to be more complete. This prevents wrong
          // simplifications like sqrt(-z^2)->%i*sqrt(z^2) for z complex.
          z = if signs.truthy() { car(signs) } else { d_csign(car(l)) }
          if simp__complex_sign_p(z) {
            z = q_d_pnz // if appears complex, unknown sign
          }
          w = if simp__neg_nz_p(z) {
            rad = cons(Fix(-1L), rad)
            mult(Fix(-1L), car(l))
          } else {
            car(l)
          }
          if onep1(w).truthy() {
            ()
          } else if alike1(w, gr).truthy() {
            return list3(list2(q_mexpt, q_simp), gr, pot)
          } else if eq(z, q_d_pn) || eq(z, q_d_pnz) {
            rad = cons(w, rad)
          } else {
            res = tms_factors(simplifya(list3(list1(q_mexpt), w, pot), t), res)
          }
          l = cdr(l)
          signs = cdr(signs)
        }
        if equal(res, list1(Fix(1L))) {
          return eqtest(list3(list1(q_mexpt), gr, pot), check)
        } else if rad is Nil {
          return testt(cons(list2(q_mtimes, q_simp), res))
        } else {
          // RADEXPAND=()?
          rad = power_star(cons(list1(q_mtimes), nreverse(rad)), pot)
          if !onep1(rad).truthy() {
            res = tms_factors(rad, res)
          }
          return eqtest(testt(cons(list1(q_mtimes), res)), check)
        }
      }
      Start => {
        if !(cdr(res) is Nil) &&
          onep1(car(res)).truthy() &&
          ratnump(cadr(res)).truthy() {
          res = cdr(res)
        }
        gr = cdr(gr)
        if gr is Nil {
          return eqtest(testt(cons(list1(q_mtimes), res)), check)
        } else if mexptp(car(gr)).truthy() {
          y = power(cadar(gr), mult(caddar(gr), pot))
        } else if eq(car(gr), q_d__pcti) {
          y = p_itopot(pot)
        } else if mnump(car(gr)).truthy() {
          y = list3(list1(q_mexpt), car(gr), pot)
        } else {
          y = list3(list2(q_mexpt, q_simp), car(gr), pot)
        }
        res = tms_factors(simplifya(y, t), res)
      }
      Retno => return exptrl(gr, pot)
      Atgr => {
        if zerop1(pot).truthy() {
          lbl = Retno
          continue
        }
        if onep1(pot).truthy() {
          let y = mget(gr, q_d_numer)
          if y.truthy() &&
            floatp(y) &&
            (symval(q_d_numer).truthy() || !equal(pot, Fix(1L))) {
            // A numeric constant like %e, %pi, ... and
            // exponent is a float or bigfloat value.
            return if memq(gr, symval(q_ear_builtin_numeric_constants)).truthy() &&
              d_bfloatp(pot).truthy() {
              // Return a bigfloat value.
              d_bfloat(gr)
            } else {
              // Return a float value.
              y
            }
          } else {
            // In all other cases exptrl simplifies accordingly.
            return exptrl(gr, pot)
          }
        } else if eq(gr, q_d__pcte) {
          // Numerically evaluate if the power is a flonum.
          let val = flonum_eval(q_p_exp, pot)
          if float_inf_p(val).truthy() {
            // needed for gcl and sbcl - (sometimes) no trap of overflow
            raise simp__float_overflow()
          }
          if val.truthy() {
            return val
          }
          // Numerically evaluate if the power is a (complex)
          // big-float.  (This is basically the guts of
          // big-float-eval, but we can't use big-float-eval.)
          if !member(q_simp, cdar(x)).truthy() &&
            complex_number_p(pot, ntypep=q_bigfloat_or_number_p).truthy() {
            let xy = trisplit(pot)
            let xr = car(xy)
            let yi = cdr(xy)
            if d_bfloatp(xr).truthy() && eql(Fix(0L), yi) {
              return d_bfloat(list3(list2(q_mexpt, q_simp), q_d__pcte, pot))
            } else if d_bfloatp(xr).truthy() || d_bfloatp(yi).truthy() {
              let mut zz = add2(d_bfloat(xr), mul2(q_d__pcti, d_bfloat(yi)))
              zz = d_rectform(list3(list2(q_mexpt, q_simp), q_d__pcte, zz))
              return d_bfloat(zz)
            }
          }
          if symval(q_d_logsimp).truthy() && among(q_p_log, pot).truthy() {
            return p_etolog(pot)
          } else if symval(q_d_demoivre).truthy() &&
            {
              z = demoivre(pot)
              z.truthy()
            } {
            return z
          } else if symval(q_d__pctemode).truthy() &&
            among(q_d__pcti, pot).truthy() &&
            among(q_d__pctpi, pot).truthy() &&
            {
              // Exponent contains %i and %pi and %emode is TRUE:
              // Check simplification of exp(%i*%pi*p/q*x)
              z = p_especial(pot)
              z.truthy()
            } {
            return z
          } else if d_taylorp(third(x)).truthy() {
            // taylorize %e^taylor(...)
            return d_taylor(x, Nil)
          }
        } else {
          let mut y = mget(gr, q_d_numer)
          // Check for a numeric constant.
          if y.truthy() &&
            floatp(y) &&
            (
              floatp(pot) ||
              // The exponent is a bigfloat. Convert base to bigfloat.
              (
                d_bfloatp(pot).truthy() &&
                memq(gr, symval(q_ear_builtin_numeric_constants)).truthy() &&
                {
                  y = d_bfloat(gr)
                  y.truthy()
                }
              ) ||
              (symval(q_d_numer).truthy() && integerp(pot))
            ) {
            return exptrl(y, pot)
          }
        }
        lbl = Up
      }
      Up => return eqtest(list3(list1(q_mexpt), gr, pot), check)
      Matrix => {
        if zerop1(pot).truthy() {
          if mxorlistp1(gr).truthy() {
            return constmx(addk(Fix(1L), pot), gr)
          } else {
            lbl = Retno
            continue
          }
        } else if onep1(pot).truthy() {
          return gr
        } else if symval(q_d_doallmxops).truthy() ||
          symval(q_d_doscmxops).truthy() ||
          symval(q_d_domxexpt).truthy() {
          if (
              mlpgr.truthy() &&
              (!d_listp(gr).truthy() || symval(q_d_listarith).truthy()) &&
              scalar_or_constant_p(pot, symval(q_d_assumescalar)).truthy()
            ) ||
            (
              symval(q_d_domxexpt).truthy() &&
              mlppot.truthy() &&
              (!d_listp(pot).truthy() || symval(q_d_listarith).truthy()) &&
              scalar_or_constant_p(gr, symval(q_d_assumescalar)).truthy()
            ) {
            return simplifya(outermap1(list([q_mexpt, gr, pot])), t)
          } else {
            lbl = Up
            continue
          }
        } else if symval(q_d_domxmxops).truthy() && simp__minus_one_p(pot) {
          return simplifya(outermap1(list([q_mexpt, gr, pot])), t)
        } else {
          lbl = Up
          continue
        }
      }
      E1 => {
        // At this point we have an expression: (z^a)^b with gr = z^a and
        // pot = b
        let bcs : Ref[Value] = { val: Nil }
        let g = gr
        let base_csign = () => {
          if !bcs.val.truthy() {
            bcs.val = d_csign(cadr(g))
          }
          bcs.val
        }
        let radexpand = symval(q_d_radexpand)
        if eq(radexpand, q_d_all) ||
          // b is an integer or an odd rational
          simplexpon(pot).truthy() ||
          (
            domain_complex() &&
            !simp__complex_sign_p(d_csign(caddr(gr))) &&
            // z >= 0 and a not a complex
            (
              simp__pos_pz_zero_p(base_csign()) ||
              // -1 < a <= 1
              (
                mnump(caddr(gr)).truthy() &&
                eq(
                  d_sign(sub(Fix(1L), take(list1(q_mabs), [caddr(gr)]))),
                  q_d_pos,
                )
              )
            )
          ) ||
          (domain_real() && simp__pos_pz_zero_p(base_csign())) ||
          // (1/z)^a -> 1/z^a when z a constant complex
          (
            eql(caddr(gr), Fix(-1L)) &&
            (
              (radexpand.truthy() && domain_real()) ||
              (
                eq(base_csign(), q_d_complex) &&
                d_constantp(cadr(gr)).truthy()
              )
            )
          ) ||
          // This does (1/z)^a -> 1/z^a. This is in general wrong.
          // We switch this type of simplification on, when
          // $ratsimpexpons is T. E.g. radcan sets this flag to T.
          (
            symval(q_d_ratsimpexpons).truthy() && equal(caddr(gr), Fix(-1L))
          ) ||
          (radexpand.truthy() && domain_real() && odnump(caddr(gr)).truthy()) {
          // Simplify (z^a)^b -> z^(a*b)
          let e = mul2(pot, caddr(gr))
          if neg_real_root_p(cadr(gr), caddr(gr), e).truthy() {
            return neg_principal_power(cadr(gr), e)
          }
          pot = e
          gr = cadr(gr)
        } else if domain_real() &&
          free(gr, q_d__pcti).truthy() &&
          radexpand.truthy() &&
          evnump(caddr(gr)).truthy() &&
          !simp__complex_sign_p(base_csign()) {
          // Simplify (x^a)^b -> abs(x)^(a*b)
          pot = mul2(pot, caddr(gr))
          gr = radmabs(cadr(gr))
        } else if radexpand.truthy() &&
          domain_real() &&
          mminusp(caddr(gr)).truthy() {
          // Simplify (1/z^a)^b -> 1/(z^a)^b
          pot = neg(pot)
          gr = power(cadr(gr), neg(caddr(gr)))
        } else {
          lbl = Up
          continue
        }
        lbl = Cont
      }
    }
  }
  Nil
}

///|
fn apparently_complex_to_judge_by__dolcsign_p(e : Value) -> Value raise {
  lbool(simp__complex_sign_p(d_csign(e)))
}

///|
fn apparently_real_to_judge_by__dolcsign_p(e : Value) -> Value raise {
  let s = d_csign(e)
  lbool(
    eq(s, q_d_pos) ||
    eq(s, q_d_neg) ||
    eq(s, q_d_zero) ||
    eq(s, q_d_pn) ||
    eq(s, q_d_pnz) ||
    eq(s, q_d_pz) ||
    eq(s, q_d_nz),
  )
}

///|
/// Returns the multiplicity of BASE in M, that is the largest k with BASE^k
/// dividing M, or NIL if there is none.
fn exponent_of(m : Value, base : Value) -> Value raise {
  let mut m = m
  let mut expo = 0L
  // Divide by BASE for as long as it goes evenly.
  while true {
    let (q, r) = num_floor(m, b=base)
    if zerop(r) {
      m = q
      expo += 1L
    } else {
      break
    }
  }
  if expo == 0L {
    Nil
  } else {
    Fix(expo)
  }
}

///|
priv enum SimpTimesinLbl {
  Top
  Start
  Less
  Less1
  Gr
  Equ
  Spcheck
  Const
  Absmerge
  Times
  Del
  PctI
}

///|
/// Multiply X^W into Y
fn timesin(x : Value, y : Value, w : Value) -> Value raise {
  let mut x = x
  let mut y = y
  let mut w = w
  let mut fm : Value = Nil
  let mut temp : Value = Nil
  let mut z : Value = Nil
  let mut check : Value = Nil
  let mut u : Value = Nil
  let mut expo : Value = Nil
  if mexptp(x).truthy() {
    check = x
  }
  let not_complex_csign = (e : Value) => !simp__complex_sign_p(d_csign(e))
  let mut lbl = SimpTimesinLbl::Top
  while true {
    match lbl {
      Top => {
        // Prepare the factor x^w and initialize the work of timesin
        if equal(w, Fix(1L)) {
          temp = x
        } else {
          temp = cons(
            list1(q_mexpt),
            if check.truthy() {
              list2(cadr(x), mult(caddr(x), w))
            } else {
              list2(x, w)
            },
          )
          if check.truthy() &&
            neg_real_root_p(cadr(x), caddr(x), caddr(temp)).truthy() {
            temp = neg_principal_power(cadr(x), caddr(temp))
          }
          if !symval(q_ear_timesinp).truthy() && !eq(x, q_d__pcti) {
            let tm = temp
            temp = with_special(q_ear_timesinp, t, () => simplifya(tm, t))
          }
          if mtimesp(temp).truthy() {
            // x^w simplified to a product, as %e^(log(u)+v) = u*%e^v does.
            // Multiply in its factors, not the product as one.
            x = temp
            lbl = Times
            continue
          }
        }
        x = if mexptp(temp).truthy() { cdr(temp) } else { list2(temp, Fix(1L)) }
        w = cadr(x)
        fm = y
        lbl = Start
      }
      Start => {
        // Go through the list of terms in fm and look what is to do.
        if cdr(fm) is Nil {
          // The list of terms is empty. The loop is finished.
          lbl = Less
          continue
        }
        if (
            mnump(temp).truthy() &&
            !(integerp(temp) || ratnump(temp).truthy())
          ) ||
          (integerp(temp) && equal(temp, Fix(-1L))) {
          // Stop the loop for a float or bigfloat number, or number -1.
          lbl = Less
          continue
        }
        if mexptp(cadr(fm)).truthy() {
          lbl = Less
          if alike1(car(x), cadadr(fm)).truthy() {
            w = plsk(caddr(cadr(fm)), w)
            if zerop1(w).truthy() {
              lbl = Del
            } else if mnump(w).truthy() &&
              (mnump(car(x)).truthy() || eq(car(x), q_d__pcti)) {
              rplacd(fm, cddr(fm)) |> ignore
              x = if mnump(car(x)).truthy() {
                let r = neg_power_product(car(x), sub(w, cadr(x)), cadr(x))
                if r.truthy() {
                  r
                } else {
                  exptrl(car(x), w)
                }
              } else {
                power(car(x), w)
              }
              if mnump(x).truthy() {
                // Do not return the number directly. Rescan it like any
                // other result. Zero is the exception: EXPONENT-OF does not
                // terminate for M = 0.
                if zerop1(x).truthy() {
                  return rplaca(y, timesk(car(y), x))
                }
                temp = x
                x = list2(x, Fix(1L))
                w = Fix(1L)
                fm = y
                lbl = Start
              } else if mtimesp(x).truthy() {
                lbl = Times
              } else {
                temp = x
                x = if mexptp(x).truthy() { cdr(x) } else { list2(x, Fix(1L)) }
                w = cadr(x)
                fm = y
                lbl = Start
              }
            } else if maxima_constantp(car(x)).truthy() {
              lbl = Const
            } else if onep1(w).truthy() {
              if mtimesp(car(x)).truthy() {
                // A base which is a mtimes expression. Remove
                // the factor from the lists of products.
                rplacd(fm, cddr(fm)) |> ignore
                // Multiply the factors of the base with
                // the list of all remaining products.
                set(q_ear_rulesw, t) |> ignore
                return muln(append(copy_list(y), copy_list(cdar(x))), t)
              } else {
                return rplaca(cdr(fm), car(x))
              }
            } else {
              lbl = Spcheck
            }
          } else if onep1(w).truthy() &&
            (
              ratnump(car(x)).truthy() ||
              (integerp(car(x)) && !onep(car(x)).truthy())
            ) {
            // At this place we have to add code for a rational number
            // as a factor to the list of products.
            // Multiplying base^k * num/den
            let num = num1(car(x))
            let den = denom1(car(x))
            let base = second(cadr(fm))
            if integerp(base) &&
              !eql(Fix(1L), num_abs(base)) &&
              {
                expo = exponent_of(num_abs(num), base)
                expo.truthy()
              } {
              // We have base^m*base^k = base^(k+m).
              temp = power(base, add2(third(cadr(fm)), expo))
              // Set fm to have 1/denom term.
              x = mul2(car(y), div(div(num, exptrl(base, expo)), den))
            } else if integerp(base) &&
              !eql(Fix(1L), num_abs(base)) &&
              {
                expo = exponent_of(den, base)
                expo.truthy()
              } {
              expo = num_neg(expo)
              // We have base^(-m)*base^k = base^(k-m).
              temp = power(base, add2(third(cadr(fm)), expo))
              // Set fm to have the numerator term.
              x = mul2(car(y), div(num, div(den, exptrl(base, num_neg(expo)))))
            } else {
              // Next term in list of products.
              fm = cdr(fm)
              lbl = Start
              continue
            }
            // Add in the base^(k+m) term or base^(k-m)
            y = rplaca(y, Fix(1L))
            rplacd(fm, cddr(fm)) |> ignore
            rplacd(fm, cons(temp, cdr(fm))) |> ignore
            temp = x
            x = list2(x, Fix(1L))
            w = Fix(1L)
            fm = y
            lbl = Start
          } else if !atom(car(x)) &&
            eq(caar(car(x)), q_mabs) &&
            equal(cadr(x), Fix(1L)) &&
            integerp(caddr(cadr(fm))) &&
            num_lt(caddr(cadr(fm)), Fix(0L)) &&
            alike1(cadr(car(x)), cadr(cadr(fm))).truthy() &&
            not_complex_csign(cadr(car(x))) {
            // 1/x^n*abs(x) -> 1/(x^(n-2)*abs(x)), where n an integer
            // Replace 1/x^n -> 1/x^(n-2)
            temp = power(cadr(cadr(fm)), add2(caddr(cadr(fm)), Fix(2L)))
            rplacd(fm, cddr(fm)) |> ignore
            if !equal(temp, Fix(1L)) {
              rplacd(fm, cons(temp, cdr(fm))) |> ignore
            }
            // Multiply factor 1/abs(x) into list of products.
            x = list2(car(x), Fix(-1L))
            temp = power(car(x), cadr(x))
            w = cadr(x)
            lbl = Start
          } else if !atom(car(x)) &&
            eq(caar(car(x)), q_mabs) &&
            equal(cadr(x), Fix(-1L)) &&
            integerp(caddr(cadr(fm))) &&
            num_gt(caddr(cadr(fm)), Fix(1L)) &&
            alike1(cadr(car(x)), cadr(cadr(fm))).truthy() &&
            not_complex_csign(cadr(car(x))) {
            // x^n/abs(x) -> x^(n-2)*abs(x), where n an integer.
            // Replace x^n -> x^(n-2)
            temp = power(cadr(cadr(fm)), add2(caddr(cadr(fm)), Fix(-2L)))
            rplacd(fm, cddr(fm)) |> ignore
            if !equal(temp, Fix(1L)) {
              rplacd(fm, cons(temp, cdr(fm))) |> ignore
            }
            // Multiply factor abs(x) into list of products.
            x = list2(car(x), Fix(1L))
            temp = power(car(x), cadr(x))
            w = cadr(x)
            lbl = Start
          } else if !atom(cadr(fm)) &&
            !atom(cadr(cadr(fm))) &&
            eq(caaadr(cadr(fm)), q_mabs) &&
            equal(caddr(cadr(fm)), Fix(-1L)) &&
            integerp(cadr(x)) &&
            num_gt(cadr(x), Fix(1L)) &&
            alike1(cadadr(cadr(fm)), car(x)).truthy() &&
            not_complex_csign(cadadr(cadr(fm))) {
            // 1/abs(x)*x^n -> x^(n-2)*abs(x), where n an integer.
            // Replace 1/abs(x) -> abs(x)
            temp = cadr(cadr(fm))
            rplacd(fm, cddr(fm)) |> ignore
            rplacd(fm, cons(temp, cdr(fm))) |> ignore
            // Multiply factor x^(n-2) into list of products.
            x = list2(car(x), add2(cadr(x), Fix(-2L)))
            temp = power(car(x), cadr(x))
            w = cadr(x)
            lbl = Start
          } else if eq(symval(q_d_domain), q_d_real) &&
            !atom(car(x)) &&
            eq(caar(car(x)), q_mabs) &&
            (integerp(cadr(x)) || ratnump(cadr(x)).truthy()) &&
            ratnump(caddr(cadr(fm))).truthy() &&
            evenp(cadr(caddr(cadr(fm)))) &&
            alike1(cadr(car(x)), cadadr(fm)).truthy() &&
            not_complex_csign(cadr(car(x))) {
            // abs(x)^b*x^a -> abs(x)^(a+b), where "a" is a ratio with an
            // even numerator, so that with domain : real, x^a is the
            // real root abs(x)^a, and b any rational number. Remove x^a.
            x = power(car(x), add2(cadr(x), caddr(cadr(fm))))
            rplacd(fm, cddr(fm)) |> ignore
            lbl = Absmerge
          } else if eq(symval(q_d_domain), q_d_real) &&
            !atom(cadr(cadr(fm))) &&
            eq(caaadr(cadr(fm)), q_mabs) &&
            (integerp(caddr(cadr(fm))) || ratnump(caddr(cadr(fm))).truthy()) &&
            ratnump(cadr(x)).truthy() &&
            evenp(cadr(cadr(x))) &&
            alike1(cadadr(cadr(fm)), car(x)).truthy() &&
            not_complex_csign(cadadr(cadr(fm))) {
            // x^a*abs(x)^b -> abs(x)^(a+b), where "a" is a ratio with an
            // even numerator and b any rational number. Remove abs(x)^b.
            x = power(cadr(cadr(fm)), add2(cadr(x), caddr(cadr(fm))))
            rplacd(fm, cddr(fm)) |> ignore
            lbl = Absmerge
          } else if maxima_constantp(car(x)).truthy() ||
            maxima_constantp(cadadr(fm)).truthy() {
            if great(temp, cadr(fm)).truthy() {
              lbl = Gr
            }
          } else if great(car(x), cadadr(fm)).truthy() {
            lbl = Gr
          }
          continue
        }
        if alike1(car(x), cadr(fm)).truthy() {
          lbl = Equ
          continue
        }
        if mnump(temp).truthy() {
          // When a number goto start and look in the next term.
          fm = cdr(fm)
          continue
        }
        if !atom(cadr(fm)) &&
          eq(caar(cadr(fm)), q_mabs) &&
          integerp(cadr(x)) &&
          num_lt(cadr(x), Fix(0L)) &&
          alike1(cadr(cadr(fm)), car(x)).truthy() &&
          not_complex_csign(cadr(cadr(fm))) {
          // abs(x)/x^n -> 1/(x^(n-2)*abs(x)), where n an integer.
          // Replace abs(x) -> 1/abs(x).
          temp = power(cadr(fm), Fix(-1L))
          rplacd(fm, cddr(fm)) |> ignore
          rplacd(fm, cons(temp, cdr(fm))) |> ignore
          // Multiply factor x^(-n+2) into list of products.
          x = list2(car(x), add2(cadr(x), Fix(2L)))
          temp = power(car(x), cadr(x))
          w = cadr(x)
          continue
        }
        if eq(symval(q_d_domain), q_d_real) &&
          !atom(cadr(fm)) &&
          eq(caar(cadr(fm)), q_mabs) &&
          ratnump(cadr(x)).truthy() &&
          evenp(cadr(cadr(x))) &&
          alike1(cadr(cadr(fm)), car(x)).truthy() &&
          not_complex_csign(cadr(cadr(fm))) {
          // x^a*abs(x) -> abs(x)^(a+1), where a a ratio with an even
          // numerator. Remove abs(x).
          x = power(cadr(fm), add2(cadr(x), Fix(1L)))
          rplacd(fm, cddr(fm)) |> ignore
          lbl = Absmerge
          continue
        }
        if maxima_constantp(car(x)).truthy() {
          if great(temp, cadr(fm)).truthy() {
            lbl = Gr
            continue
          }
        } else if great(car(x), cadr(fm)).truthy() {
          lbl = Gr
          continue
        }
        lbl = Less
      }
      Less => {
        if mnump(temp).truthy() {
          // Multiply a number into the list of products.
          temp = timesk(car(y), temp)
          if !onep1(car(y)).truthy() &&
            (
              ratnump(temp).truthy() ||
              (integerp(temp) && !onep(temp).truthy() && !zerop(temp))
            ) {
            // The new coefficient can combine with a power of an integer
            // base, even though neither factor did. Rescan the list of
            // products with it.
            rplaca(y, Fix(1L)) |> ignore
            x = list2(temp, Fix(1L))
            w = Fix(1L)
            fm = y
            lbl = Start
            continue
          } else {
            return rplaca(y, temp)
          }
        }
        if eq(car(x), q_d__pcti) && fixnump(w) {
          lbl = PctI
          continue
        }
        if eq(car(x), q_d__pcte) && symval(q_d_numer).truthy() && integerp(w) {
          return rplaca(y, timesk(car(y), lexp(lfloat(w))))
        }
        if onep1(w).truthy() && !constant(car(x)).truthy() {
          lbl = Less1
          continue
        }
        // At this point we will insert a mexpt expression,
        // but first we look at the car of the list of products and
        // modify the expression if we found a rational number.
        if mexptp(temp).truthy() &&
          !onep1(car(y)).truthy() &&
          (integerp(car(y)) || ratnump(car(y)).truthy()) {
          // Multiplying base^k * num/den.
          let num = num1(car(y))
          let den = denom1(car(y))
          let base = car(x)
          if integerp(base) &&
            !eql(Fix(1L), num_abs(base)) &&
            {
              expo = exponent_of(num_abs(num), base)
              expo.truthy()
            } {
            // We have base^m*base^k.
            temp = power(base, add2(cadr(x), expo))
            // Set fm to have 1/denom term.
            x = div(div(num, exptrl(base, expo)), den)
          } else if integerp(base) &&
            !eql(Fix(1L), num_abs(base)) &&
            {
              expo = exponent_of(den, base)
              expo.truthy()
            } {
            expo = num_neg(expo)
            // We have base^(-m)*base^k.
            temp = power(base, add2(cadr(x), expo))
            // Set fm to have the numerator term.
            x = div(num, div(den, exptrl(base, num_neg(expo))))
          } else {
            // The rational doesn't contain any (simple) powers of
            // the exponential term.  We're done.
            return cdr(rplacd(fm, cons(temp, cdr(fm))))
          }
          // Add in the a^(m+k) or a^(k-m) term.
          y = rplaca(y, Fix(1L))
          rplacd(fm, cons(temp, cdr(fm))) |> ignore
          temp = x
          x = list2(x, Fix(1L))
          w = Fix(1L)
          fm = y
          lbl = Start
          continue
        }
        if maxima_constantp(car(x)).truthy() &&
          {
            let mut found = false
            let mut l = cdr(fm)
            while !(cdr(l) is Nil) {
              if mexptp(cadr(l)).truthy() && alike1(car(x), cadadr(l)).truthy() {
                fm = l
                found = true
                break
              }
              l = cdr(l)
            }
            found
          } {
          lbl = Start
          continue
        }
        if (mnump(car(x)).truthy() && mnump(w).truthy()) ||
          (
            eq(car(x), q_d__pcte) &&
            symval(q_d__pctemode).truthy() &&
            among(q_d__pcti, w).truthy() &&
            among(q_d__pctpi, w).truthy() &&
            {
              u = p_especial(w)
              u.truthy()
            }
          ) {
          x = if u.truthy() {
            u
          } else if alike(cdr(check), x).truthy() {
            check
          } else {
            exptrl(car(x), w)
          }
          if mnump(x).truthy() {
            return rplaca(y, timesk(car(y), x))
          } else if mtimesp(x).truthy() {
            lbl = Times
            continue
          } else if mexptp(x).truthy() {
            return cdr(rplacd(fm, cons(x, cdr(fm))))
          } else {
            temp = x
            x = list2(x, Fix(1L))
            w = Fix(1L)
            fm = y
            lbl = Start
            continue
          }
        }
        if onep1(w).truthy() {
          lbl = Less1
          continue
        }
        temp = list3(list1(q_mexpt), car(x), w)
        temp = eqtest(temp, if check.truthy() {
          check
        } else {
          list1(list1(q_foo))
        })
        return cdr(rplacd(fm, cons(temp, cdr(fm))))
      }
      Less1 => return cdr(rplacd(fm, cons(car(x), cdr(fm))))
      Gr => {
        fm = cdr(fm)
        lbl = Start
      }
      Equ => {
        if eq(car(x), q_d__pcti) && equal(w, Fix(1L)) {
          rplacd(fm, cddr(fm)) |> ignore
          return rplaca(y, timesk(Fix(-1L), car(y)))
        }
        w = plsk(Fix(1L), w)
        if zerop1(w).truthy() {
          lbl = Del
          continue
        }
        if mnump(car(x)).truthy() && mnump(w).truthy() {
          return rplaca(cdr(fm), exptrl(car(x), w))
        }
        if maxima_constantp(car(x)).truthy() {
          lbl = Const
          continue
        }
        lbl = Spcheck
      }
      Spcheck => {
        z = list3(list1(q_mexpt), car(x), w)
        x = simplifya(z, t)
        if alike1(x, z).truthy() {
          // Extract the merged term and re-insert it into the product
          // so it can trigger simplifications with existing factors.
          // This is necessary to make x/abs(x)*x -> abs(x) work.
          rplacd(fm, cddr(fm)) |> ignore
          temp = x
          x = if mexptp(x).truthy() { cdr(x) } else { list2(x, Fix(1L)) }
          w = cadr(x)
          fm = y
          lbl = Start
        } else {
          rplacd(fm, cddr(fm)) |> ignore
          set(q_ear_rulesw, t) |> ignore
          return muln(cons(x, y), t)
        }
      }
      Const => {
        rplacd(fm, cddr(fm)) |> ignore
        x = car(x)
        check = Nil
        lbl = Top
      }
      Absmerge => {
        // Rescan the list of products with the merged power of abs(x).
        if mnump(x).truthy() {
          return rplaca(y, timesk(car(y), x))
        } else if mtimesp(x).truthy() {
          lbl = Times
        } else {
          temp = x
          x = if mexptp(x).truthy() { cdr(x) } else { list2(x, Fix(1L)) }
          w = cadr(x)
          fm = y
          lbl = Start
        }
      }
      Times => {
        temp = cons(list1(q_mtimes), y)
        z = tms(x, Fix(1L), temp)
        return if physical_equal_value(z, temp) {
          cdr(z)
        } else {
          set(q_ear_rulesw, t) |> ignore
          z
        }
      }
      Del => return rplacd(fm, cddr(fm))
      PctI => {
        w = num_rem(w, Fix(4L))
        if minusp(w) {
          w = num_add(w, Fix(4L))
        }
        return if zerop(w) {
          fm
        } else if num_eq(w, Fix(2L)) {
          rplaca(y, timesk(Fix(-1L), car(y)))
        } else if num_eq(w, Fix(3L)) {
          rplaca(y, timesk(Fix(-1L), car(y))) |> ignore
          rplacd(fm, cons(q_d__pcti, cdr(fm)))
        } else {
          rplacd(fm, cons(q_d__pcti, cdr(fm)))
        }
      }
    }
  }
  Nil
}
