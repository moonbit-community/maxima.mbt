// Port of share/simplification/scifac.lisp: GCFAC, a fast factoring
// routine which factors out monomials and common integer coefficients
// (destructively, on a copy of the expression).

///|
/// macro MAKE-EXPT: `((mexpt simp) ,base ,exponent)
fn make_expt(base : Value, exponent : Value) -> Value raise {
  list3(list2(q_mexpt, q_simp), base, exponent)
}

///|
/// macro ACCEPTABLE-POWER: it refers to local variables of
/// FACTOROUT-MONOMIAL and returns from its enclosing DO, so it is expanded
/// there (scifac__acceptable_power) and cannot be called.
fn acceptable_power(x : Value) -> Value raise {
  ignore(x)
  lisp_error("ACCEPTABLE-POWER is a macro expanded inline in FACTOROUT-MONOMIAL")
}

///|
/// Outcome of an expansion of ACCEPTABLE-POWER.
priv enum ScifacAp {
  Yes
  No
  ReturnNil // (return nil) from the enclosing DO
}

///|
/// The expansion of ACCEPTABLE-POWER on X with EXPON its exponent: MINPOW
/// is updated in place.
fn scifac__acceptable_power(
  x : Value,
  expon : Value,
  var_ : Value,
  minpow : Ref[Value],
  nstate : Bool,
  number : Bool,
  expon_sign : Bool,
) -> ScifacAp raise {
  if alike1(cadr(x), var_) is Nil {
    return No
  }
  minpow.val = if nstate {
    if integerp(expon) {
      num_min(minpow.val, expon)
    } else {
      Nil
    }
  } else if number {
    if d_numberp(expon).truthy() && integerp(sub(minpow.val, expon)) {
      mfuncall(q_d_min, list2(minpow.val, expon))
    } else {
      Nil
    }
  } else {
    let powdif = sub(minpow.val, expon)
    if integerp(powdif) {
      if num_gt(powdif, Fix(0L)) {
        expon
      } else {
        minpow.val
      }
    } else {
      let g = d_gcd(minpow.val, expon, Nil)
      let d1 = d_ratsimp(div(minpow.val, g), Nil)
      let d2 = d_ratsimp(div(expon, g), Nil)
      if integerp(d1) && integerp(d2) {
        if num_gt(d1, d2) {
          expon
        } else {
          minpow.val
        }
      } else {
        Nil
      }
    }
  }
  if minpow.val is Nil {
    return No
  }
  let s = if number {
    mnegp(expon).truthy()
  } else if mtimesp(expon).truthy() {
    equal(Fix(-1L), cadr(expon))
  } else {
    false
  }
  if expon_sign == s {
    Yes
  } else {
    ReturnNil
  }
}

///|
/// `(,@l ,x)`
fn scifac__snoc(l : Value, x : Value) -> Value raise {
  append(l, list1(x))
}

///|
fn factorout_monomial(exp_ : Value) -> Value raise {
  let exp = exp_
  let mut monomials : Value = Nil
  let lead_term = cadr(exp)
  let mut alone = true
  let mut minuslogic = length(exp) > 3 &&
    {
      let minusobj = car(last(exp))
      if integerp(minusobj) {
        minusp(minusobj)
      } else if mtimesp(minusobj).truthy() {
        integerp(cadr(minusobj)) && minusp(cadr(minusobj))
      } else {
        false
      }
    }
  let mut rem_prod : Value = if d_mapatom(lead_term).truthy() ||
    eq(caar(lead_term), q_mexpt) {
    list1(lead_term)
  } else if eq(caar(lead_term), q_mtimes) {
    alone = false
    cdr(lead_term)
  } else {
    Nil
  }
  let mut follow = lead_term
  let mut j = 1
  while rem_prod.truthy() {
    let potentl_mon = car(rem_prod)
    let mut truth = false
    let leadfix = integerp(potentl_mon)
    if leadfix || minuslogic {
      let mut intgcd : Value = if leadfix {
        potentl_mon
      } else {
        if alone {
          rplaca(cdr(exp), list3(list2(q_mtimes, q_simp), Fix(1L), potentl_mon))
          |> ignore
          rem_prod = cdadr(exp)
          alone = false
        } else {
          rplacd(follow, append(list1(Fix(1L)), rem_prod)) |> ignore
          rem_prod = cdr(follow)
        }
        Fix(1L)
      }
      let mut single = list1(lbool(leadfix && alone))
      let mut ge = cddr(exp)
      let mut all_minus = minusp(intgcd)
      let mut returned = false
      while ge.truthy() {
        let leadnum = car(ge)
        if integerp(leadnum) {
          single = scifac__snoc(single, t)
          intgcd = num_gcd(intgcd, leadnum)
          all_minus = all_minus && minusp(leadnum)
        } else if mtimesp(leadnum).truthy() {
          let numb = cadr(leadnum)
          if integerp(numb) {
            single = scifac__snoc(single, Nil)
            intgcd = num_gcd(intgcd, numb)
            all_minus = all_minus && minusp(numb)
          } else if minuslogic {
            single = scifac__snoc(single, Nil)
            intgcd = Fix(1L)
            rplacd(leadnum, append(list1(Fix(1L)), cdr(leadnum))) |> ignore
          } else {
            returned = true
            break
          }
        } else if minuslogic {
          single = scifac__snoc(single, Nil)
          intgcd = Fix(1L)
          rplaca(ge, list3(list2(q_mtimes, q_simp), Fix(1L), leadnum)) |> ignore
        } else {
          returned = true
          break
        }
        ge = cdr(ge)
      }
      if !returned {
        if minuslogic || all_minus {
          if !minusp(intgcd) {
            intgcd = num_neg(intgcd)
          }
          minuslogic = false
        }
        if !equal(intgcd, Fix(1L)) {
          monomials = scifac__snoc(monomials, intgcd)
          let mut redu_const = cdr(exp)
          let mut in_follow = exp
          let mut logic = single
          while redu_const.truthy() {
            let term1 = car(redu_const)
            if car(logic).truthy() {
              rplaca(redu_const, num_truncate(term1, b=intgcd).0) |> ignore
            } else if equal(
                Fix(1L),
                car(rplaca(cdr(term1), num_truncate(cadr(term1), b=intgcd).0)),
              ) {
              if physical_equal_value(logic, single) {
                j = j - 1
                rem_prod = follow
              }
              rplacd(term1, cddr(term1)) |> ignore
              if cddr(term1) is Nil {
                let pluscontac = cadr(term1)
                if mplusp(pluscontac).truthy() {
                  rplacd(in_follow, append(cdr(pluscontac), cdr(redu_const)))
                  |> ignore
                  redu_const = nthcdr(length(pluscontac) - 1, in_follow)
                  if physical_equal_value(logic, single) {
                    let new_lead = cadr(exp)
                    if mtimesp(new_lead).truthy() {
                      rem_prod = new_lead
                    } else {
                      alone = true
                      rem_prod = list2(Nil, new_lead)
                    }
                  }
                } else {
                  rplaca(redu_const, pluscontac) |> ignore
                  if physical_equal_value(logic, single) {
                    alone = true
                  }
                }
              }
            }
            in_follow = redu_const
            redu_const = cdr(redu_const)
            logic = cdr(logic)
          }
        }
      }
    } else {
      if !d_mapatom(potentl_mon).truthy() {
        truth = eq(caar(potentl_mon), q_mexpt)
      }
      let mut power = list1(if truth { caddr(potentl_mon) } else { Fix(1L) })
      let mut place = list1(if alone { Fix(-1L) } else { int(j) })
      let var_ = if truth { cadr(potentl_mon) } else { potentl_mon }
      let minpow : Ref[Value] = Ref(car(power))
      let number = d_numberp(minpow.val).truthy()
      let mut ge = cddr(exp)
      let expon_sign = truth &&
        (
          if number {
            mnegp(minpow.val).truthy()
          } else if mtimesp(minpow.val).truthy() {
            equal(Fix(-1L), cadr(minpow.val))
          } else {
            false
          }
        )
      let nstate = integerp(minpow.val)
      let mut returned = false
      while ge.truthy() {
        let exam_term = car(ge)
        if d_mapatom(exam_term).truthy() {
          if nstate && alike1(exam_term, var_).truthy() {
            place = scifac__snoc(place, Fix(-1L))
            minpow.val = Fix(1L)
            power = scifac__snoc(power, Fix(1L))
          } else {
            returned = true
            break
          }
        } else if eq(caar(exam_term), q_mexpt) {
          let expon = caddr(exam_term)
          match
            scifac__acceptable_power(
              exam_term, expon, var_, minpow, nstate, number, expon_sign,
            ) {
            Yes => {
              place = scifac__snoc(place, Fix(-2L))
              power = scifac__snoc(power, expon)
            }
            _ => {
              returned = true
              break
            }
          }
        } else if eq(caar(exam_term), q_mtimes) {
          // the DO over the factors returns T when one of them fits
          let mut found = false
          let mut pick = cdr(exam_term)
          let mut k = 1
          while pick.truthy() {
            let morcel = car(pick)
            if d_mapatom(morcel).truthy() {
              if nstate && alike1(morcel, var_).truthy() {
                place = scifac__snoc(place, int(k))
                minpow.val = Fix(1L)
                power = scifac__snoc(power, Fix(1L))
                found = true
                break
              }
            } else if eq(caar(morcel), q_mexpt) {
              let expon = caddr(morcel)
              match
                scifac__acceptable_power(
                  morcel, expon, var_, minpow, nstate, number, expon_sign,
                ) {
                Yes => {
                  place = scifac__snoc(place, int(k))
                  power = scifac__snoc(power, expon)
                  found = true
                  break
                }
                No => ()
                ReturnNil => break
              }
            } else if nstate && alike1(morcel, var_).truthy() {
              if expon_sign {
                break
              }
              place = scifac__snoc(place, int(k))
              minpow.val = Fix(1L)
              power = scifac__snoc(power, Fix(1L))
              found = true
              break
            }
            pick = cdr(pick)
            k = k + 1
          }
          if !found {
            returned = true
            break
          }
        } else if nstate && alike1(exam_term, var_).truthy() && !expon_sign {
          place = scifac__snoc(place, Fix(-1L))
          minpow.val = Fix(1L)
          power = scifac__snoc(power, Fix(1L))
        } else {
          returned = true
          break
        }
        ge = cdr(ge)
      }
      if !returned {
        if !number && expon_sign {
          minpow.val = mul2(Fix(-1L), minpow.val)
        }
        let minpow = minpow.val
        monomials = scifac__snoc(monomials, if equal(minpow, Fix(1L)) {
          var_
        } else {
          make_expt(cadr(potentl_mon), minpow)
        })
        let mut deflate = cdr(exp)
        let mut d_follow = exp
        let mut pl = place
        let mut pow = power
        while deflate.truthy() {
          let pownum = car(pow)
          let plnum = car(pl)
          let same = if nstate {
            equal(pownum, minpow)
          } else {
            alike1(pownum, minpow).truthy()
          }
          let next = if nstate {
            equal(pownum, num_add(minpow, Fix(1L)))
          } else {
            alike1(pownum, add2(Fix(1L), minpow)).truthy()
          }
          if minusp(plnum) {
            if same {
              rplaca(deflate, Fix(1L)) |> ignore
            } else if next {
              rplaca(deflate, cadar(deflate)) |> ignore
            } else {
              rplaca(cddar(deflate), if nstate { num_sub(pownum, minpow) } else { sub(pownum, minpow) }) |> ignore
            }
          } else {
            let term = car(deflate)
            let point = nthcdr(to_int(plnum), term)
            if same {
              rplacd(nthcdr(to_int(plnum) - 1, term), cdr(point)) |> ignore
              if physical_equal_value(pl, place) {
                j = j - 1
                rem_prod = follow
              }
              if cddr(term) is Nil {
                let pluscontac = cadr(term)
                if mplusp(pluscontac).truthy() {
                  rplacd(d_follow, append(cdr(pluscontac), cdr(deflate)))
                  |> ignore
                  deflate = nthcdr(length(pluscontac) - 1, d_follow)
                  if physical_equal_value(pl, place) {
                    let new_lead = cadr(exp)
                    if mtimesp(new_lead).truthy() {
                      rem_prod = new_lead
                    } else {
                      alone = true
                      rem_prod = list2(Nil, new_lead)
                    }
                  }
                } else {
                  rplaca(deflate, pluscontac) |> ignore
                  if physical_equal_value(pl, place) {
                    alone = true
                  }
                }
              }
            } else if next {
              rplaca(point, cadar(point)) |> ignore
            } else {
              rplaca(cddar(point), if nstate { num_sub(pownum, minpow) } else { sub(pownum, minpow) }) |> ignore
            }
          }
          d_follow = deflate
          deflate = cdr(deflate)
          pl = cdr(pl)
          pow = cdr(pow)
        }
      }
    }
    follow = rem_prod
    rem_prod = cdr(rem_prod)
    j = j + 1
  }
  if monomials is Nil {
    exp
  } else {
    with_special(q_d_negdistrib, Nil, () => muln(
      append(monomials, list1(addn(cdr(exp), Nil))),
      Nil,
    ))
  }
}

///|
fn pair_factor(gel : Value, flag : Value) -> Value raise {
  if flag.truthy() && (d_mapatom(gel).truthy() || cdddr(gel) is Nil) {
    return gel
  }
  let mut lcl = cdr(gel)
  let mut backpnt = gel
  while cdr(lcl).truthy() {
    let pntr = add2(car(lcl), cadr(lcl))
    let mut g = factorout_monomial(pntr)
    if !physical_equal_value(pntr, g) {
      let again = more_subfactors_q(g)
      if !physical_equal_value(again, g) {
        g = again
      }
      rplaca(lcl, g) |> ignore
      let exp = cddr(lcl)
      rplacd(lcl, exp) |> ignore
      if exp.truthy() {
        pair_factor(backpnt, Nil) |> ignore
      }
      return if cddr(gel) is Nil { cadr(gel) } else { gel }
    }
    backpnt = lcl
    lcl = cdr(lcl)
  }
  gel
}

///|
fn more_subfactors_q(gg : Value) -> Value raise {
  if eq(caar(gg), q_mtimes) {
    let mut lom = cdr(gg)
    let mut modified = false
    let mut back = gg
    while lom.truthy() {
      let obj = car(lom)
      if mplusp(obj).truthy() {
        let pntr = pair_factor(obj, t)
        if !physical_equal_value(pntr, obj) {
          let fit = cdr(pntr)
          rplacd(back, append(fit, cdr(lom))) |> ignore
          lom = nthcdr(length(fit), back)
          modified = true
        }
      }
      back = lom
      lom = cdr(lom)
    }
    if modified {
      muln(cdr(gg), t)
    } else {
      gg
    }
  } else {
    pair_factor(gg, t)
  }
}

///|
fn gcfac_prodscan(x : Value) -> Value raise {
  let mut inlev = cdr(x)
  let mut modified = false
  let mut backpnt = x
  while inlev.truthy() {
    let possibl_sum = car(inlev)
    let pntr = monomial_factor(possibl_sum)
    if !physical_equal_value(pntr, possibl_sum) {
      let fit = cdr(pntr)
      rplacd(backpnt, append(fit, cdr(inlev))) |> ignore
      inlev = nthcdr(length(fit), backpnt)
      modified = true
    }
    backpnt = inlev
    inlev = cdr(inlev)
  }
  if modified {
    muln(cdr(x), t)
  } else {
    x
  }
}

///|
fn monomial_factor(exp_ : Value) -> Value raise {
  let exp = exp_
  if d_mapatom(exp).truthy() {
    exp
  } else if eq(caar(exp), q_mtimes) {
    gcfac_prodscan(exp)
  } else if eq(caar(exp), q_mplus) {
    let mut mlm = cdr(exp)
    while mlm.truthy() {
      let potenl_prod = car(mlm)
      if mtimesp(potenl_prod).truthy() {
        let w = gcfac_prodscan(potenl_prod)
        if !physical_equal_value(w, potenl_prod) {
          rplaca(mlm, w) |> ignore
        }
      } else {
        monomial_factor(potenl_prod) |> ignore
      }
      mlm = cdr(mlm)
    }
    more_subfactors_q(factorout_monomial(exp))
  } else {
    let mut mlm = cdr(exp)
    while mlm.truthy() {
      let obj = car(mlm)
      let res = monomial_factor(obj)
      if !physical_equal_value(obj, res) {
        rplaca(mlm, res) |> ignore
      }
      mlm = cdr(mlm)
    }
    exp
  }
}

///|
fn d_gcfac(x : Value) -> Value raise {
  if d_mapatom(x).truthy() {
    x
  } else {
    monomial_factor(copy_tree(d_totaldisrep(x)))
  }
}

///|
/// Top-level forms of scifac.lisp.
fn init_share_scifac() -> Unit raise {
  macsyma_module(sym("scifac"), Nil) |> ignore
}
