// Port of src/numth.lisp, part 2: GALOIS FIELDS -- settings, coefficient
// arithmetic, setting the field, conversions, and the polynomial arithmetic.
//
// The following is a revision and improvement of the first part of share/
// contrib/gf/gf.mac by Alasdair McAndrew, Fabrizio Caruso and Jacopo
// D'Aurizio released under terms of the GPLv2 in 2007.
//
// 2012 - 2014, Volker van Nek

///|
fn numth__gf_char() -> Value {
  symval(q_ear_gf_char)
}

///|
fn numth__gf_red() -> Value {
  symval(q_ear_gf_red)
}

///|
fn numth__ef_red() -> Value {
  symval(q_ear_ef_red)
}

///|
fn numth__gf_ord() -> Value {
  symval(q_ear_gf_ord)
}

///|
fn numth__gf_card() -> Value {
  symval(q_ear_gf_card)
}

///|
/// "ef" or "gf" for error messages.
fn numth__ef_gf_str() -> Value {
  Str(if numth__efp() { "ef" } else { "gf" })
}

///|
fn numth__quotient_by_zero() -> Value raise {
  numth__err("~m arithmetic: Quotient by zero", [numth__ef_gf_str()])
}

///|
/// `(svref v i)` for an integer Value i.
fn numth__svref(v : Value, i : Value) -> Value raise {
  aref1(v, to_int(i))
}

///|
fn gf_balanced_info(assign_var : Value, arg : Value) -> Value raise {
  ignore(assign_var)
  set(q_d_gf_balanced, arg) |> ignore
  format(
    t,
    "`gf_symmetric' is deprecated and replaced by `gf_balanced'.~%The value is bound to `gf_balanced'.",
    [],
  )
}

///|
fn gf_coeff_check(assign_var : Value, arg : Value) -> Value raise {
  ignore(assign_var)
  if !(integerp(arg) && num_gt(arg, Fix(1L))) {
    numth__err(
      "`gf_coeff_limit': Assignment ignored. Value must be an integer greater than 1.~%",
      [],
    )
  } else {
    Nil
  }
}

///|
/// contains parts of merror.lisp/merror but avoids "To debug this ...".
fn gf_merror(sstring : Value, l : Value) -> Value raise {
  set(q_d_error, cons(list1(q_mlist), cons(sstring, l))) |> ignore
  if symval(q_d_errormsg).truthy() {
    d_errormsg() |> ignore
  }
  fresh_line() |> ignore
  format(t, "~& -- an error.~%", []) |> ignore
  throw_tag(q_macsyma_quit, q_maxima_error)
}

///|
fn gf_char_q(fun : Value) -> Value raise {
  if symval(q_ear_gf_char_q).truthy() {
    t
  } else {
    numth__err("`~m': The characteristic is not defined yet.", [fun])
  }
}

///|
fn gf_red_q(fun : Value) -> Value raise {
  if symval(q_ear_gf_red_q).truthy() {
    t
  } else {
    numth__err("`~m': The reduction polynomial is not defined yet.", [fun])
  }
}

///|
fn gf_data_q(fun : Value) -> Value raise {
  if symval(q_ear_gf_data_q).truthy() {
    t
  } else {
    numth__err("`~m': gf_set_data called?", [fun])
  }
}

///|
fn gf_field_q(fun : Value) -> Value raise {
  if gf_data_q(fun).truthy() && symval(q_ear_gf_irred_q).truthy() {
    t
  } else {
    numth__err("`~m': The reduction polynomial is not irreducible.", [fun])
  }
}

///|
fn ef_gf_field_q(fun : Value) -> Value raise {
  if symval(q_ear_gf_data_q).truthy() && symval(q_ear_gf_irred_q).truthy() {
    t
  } else {
    numth__err("`~m': The base field is not defined yet.", [fun])
  }
}

///|
fn ef_red_q(fun : Value) -> Value raise {
  if ef_gf_field_q(fun).truthy() && symval(q_ear_ef_red_q).truthy() {
    t
  } else {
    numth__err("`~m': The reduction polynomial is not defined yet.", [fun])
  }
}

///|
fn ef_data_q(fun : Value) -> Value raise {
  if ef_gf_field_q(fun).truthy() && symval(q_ear_ef_data_q).truthy() {
    t
  } else {
    numth__err("`~m': ef_set_data called?", [fun])
  }
}

///|
fn ef_field_q(fun : Value) -> Value raise {
  if ef_data_q(fun).truthy() && symval(q_ear_ef_irred_q).truthy() {
    t
  } else {
    numth__err("`~m': The extension is no field.", [fun])
  }
}

// basic coefficient arithmetic ------------------------------------------------
//
// *ef-arith?* controls coefficient arithmetic. If *ef-arith?* is false,
// coeffs are elements of Zp, where p is the defined characteristic *gf-char*.
// If *ef-arith?* is true, coeffs are interpreted as the integer
// representation of a polynomial over Zp[x] reduced by the irreducible
// polynomial *gf-red*.

///|
fn gf_cinv(c : Value) -> Value raise {
  if numth__efp() {
    ef_cinv(c)
  } else if numth__eqi(c, 0) {
    numth__err("gf coefficient inversion: Quotient by zero", [])
  } else {
    inv_mod(c, numth__gf_char()) // *gf-char* is prime
  }
}

///|
fn gf_cpow(c : Value, n : Value) -> Value raise {
  if numth__efp() {
    ef_cpow(c, n)
  } else {
    power_mod(c, n, numth__gf_char())
  }
}

///|
fn gf_cmod(c : Value) -> Value raise {
  if numth__efp() {
    ef_cmod(c)
  } else {
    num_mod(c, numth__gf_char())
  }
}

///|
fn gf_ctimes(a : Value, b : Value) -> Value raise {
  if numth__efp() {
    ef_ctimes(a, b)
  } else {
    num_mod(num_mul(a, b), numth__gf_char())
  }
}

///|
/// assumes that both 0 <= a,b < *gf-char*
fn gf_cplus_b(a : Value, b : Value) -> Value raise {
  if numth__efp() {
    ef_cplus_b(a, b)
  } else {
    let s = num_add(a, b)
    let p = numth__gf_char()
    if num_lt(s, p) {
      s
    } else {
      num_sub(s, p)
    }
  }
}

///|
/// assumes that 0 <= c < *gf-char*
fn gf_cminus_b(c : Value) -> Value raise {
  if numth__eqi(c, 0) {
    Fix(0L)
  } else if numth__eqi(numth__gf_char(), 2) {
    c
  } else if numth__efp() {
    ef_cminus_b(c)
  } else {
    num_sub(numth__gf_char(), c)
  }
}

// ef coefficient arith :

///|
fn ef_cinv(c : Value) -> Value raise {
  if numth__eqi(c, 0) {
    numth__err("ef coefficient inversion: Quotient by zero", [])
  } else if symval(q_d_ef_coeff_inv).truthy() {
    mfuncall(q_d_ef_coeff_inv, list1(c))
  } else if symval(q_ear_gf_logs_q).truthy() {
    ef_cinv_by_table(c)
  } else if numth__eqi(numth__gf_char(), 2) {
    f2_inv(c)
  } else {
    numth__ef(Nil, fn() { gf_x2n(gf_inv(gf_n2x(c), numth__gf_red())) })
  }
}

///|
fn ef_cpow(c : Value, n : Value) -> Value raise {
  if symval(q_d_ef_coeff_exp).truthy() {
    mfuncall(q_d_ef_coeff_exp, list2(c, n))
  } else if symval(q_ear_gf_logs_q).truthy() {
    ef_cpow_by_table(c, n)
  } else if numth__eqi(numth__gf_char(), 2) {
    f2_pow(c, n)
  } else {
    numth__ef(Nil, fn() { gf_x2n(gf_pow(gf_n2x(c), n, numth__gf_red())) })
  }
}

///|
fn ef_cmod(c : Value) -> Value raise {
  if plusp(c) {
    if num_lt(c, numth__gf_ord()) {
      c
    } else if numth__eqi(numth__gf_char(), 2) {
      f2_red(c)
    } else {
      numth__ef(Nil, fn() { gf_x2n(gf_nred(gf_n2x(c), numth__gf_red())) })
    }
  } else {
    let c = ef_cmod(num_abs(c))
    numth__ef(t, fn() { gf_ctimes(one_minus(numth__gf_char()), c) })
  }
}

///|
fn ef_ctimes(a : Value, b : Value) -> Value raise {
  if symval(q_d_ef_coeff_mult).truthy() {
    mfuncall(q_d_ef_coeff_mult, list2(a, b))
  } else if symval(q_ear_gf_logs_q).truthy() {
    ef_ctimes_by_table(a, b)
  } else if numth__eqi(numth__gf_char(), 2) {
    f2_times(a, b)
  } else {
    numth__ef(Nil, fn() {
      gf_x2n(gf_times(gf_n2x(a), gf_n2x(b), numth__gf_red()))
    })
  }
}

///|
fn ef_cplus_b(a : Value, b : Value) -> Value raise {
  if numth__eqi(numth__gf_char(), 2) {
    logxor(a, b)
  } else if symval(q_d_ef_coeff_add).truthy() {
    mfuncall(q_d_ef_coeff_add, list2(a, b))
  } else if symval(q_ear_gf_logs_q).truthy() {
    ef_cplus_by_table(a, b)
  } else {
    numth__ef(Nil, fn() { gf_x2n(gf_nplus(gf_n2x(a), gf_n2x(b))) })
  }
}

///|
fn ef_cminus_b(a : Value) -> Value raise {
  if numth__eqi(a, 0) {
    Fix(0L)
  } else if numth__eqi(numth__gf_char(), 2) {
    a
  } else if symval(q_d_ef_coeff_mult).truthy() {
    mfuncall(q_d_ef_coeff_mult, list2(one_minus(numth__gf_char()), a))
  } else if symval(q_ear_gf_logs_q).truthy() {
    ef_cminus_by_table(a)
  } else {
    numth__ef(Nil, fn() { gf_x2n(gf_nminus(gf_n2x(a))) })
  }
}

// ef coefficient arith by lookup:

///|
fn ef_ctimes_by_table(c : Value, d : Value) -> Value raise {
  if numth__eqi(c, 0) || numth__eqi(d, 0) {
    Fix(0L)
  } else {
    let logs = symval(q_d_gf_logs)
    let cd = num_add(numth__svref(logs, c), numth__svref(logs, d))
    let ord = numth__gf_ord()
    numth__svref(
      symval(q_d_gf_powers),
      if num_lt(cd, ord) {
        cd
      } else {
        num_sub(cd, ord)
      },
    )
  }
}

///|
fn ef_cminus_by_table(c : Value) -> Value raise {
  if numth__eqi(c, 0) {
    Fix(0L)
  } else if numth__eqi(numth__gf_char(), 2) {
    c
  } else {
    let e = ash(numth__gf_ord(), -1)
    let c = numth__svref(symval(q_d_gf_logs), c)
    numth__svref(
      symval(q_d_gf_powers),
      if num_lt(c, e) {
        num_add(c, e)
      } else {
        num_sub(c, e)
      },
    )
  }
}

///|
fn ef_cinv_by_table(c : Value) -> Value raise {
  if numth__eqi(c, 0) {
    numth__err("ef coefficient inversion: Quotient by zero", [])
  } else {
    numth__svref(
      symval(q_d_gf_powers),
      num_sub(numth__gf_ord(), numth__svref(symval(q_d_gf_logs), c)),
    )
  }
}

///|
fn ef_cplus_by_table(c : Value, d : Value) -> Value raise {
  if numth__eqi(c, 0) {
    d
  } else if numth__eqi(d, 0) {
    c
  } else {
    let logs = symval(q_d_gf_logs)
    let c = numth__svref(logs, c)
    let d = numth__svref(logs, d)
    let ord = numth__gf_ord()
    let z = numth__svref(
      symval(q_d_gf_zech_logs),
      if num_lt(d, c) {
        num_add(ord, num_sub(d, c))
      } else {
        num_sub(d, c)
      },
    )
    if z.truthy() {
      let z = num_add(z, c)
      numth__svref(
        symval(q_d_gf_powers),
        if num_gt(z, ord) {
          num_sub(z, ord)
        } else {
          z
        },
      )
    } else {
      Fix(0L)
    }
  }
}

///|
fn ef_cpow_by_table(c : Value, n : Value) -> Value raise {
  if numth__eqi(n, 0) {
    Fix(1L)
  } else if numth__eqi(c, 0) {
    Fix(0L)
  } else {
    numth__svref(
      symval(q_d_gf_powers),
      num_mod(
        num_mul(n, numth__svref(symval(q_d_gf_logs), c)),
        numth__gf_ord(),
      ),
    )
  }
}

///|
/// table lookup uses current *gf-red* for reduction
fn gf_pow_by_table(x : Value, n : Value) -> Value raise {
  if numth__eqi(n, 0) {
    list2(Fix(0L), Fix(1L))
  } else if x is Nil {
    Nil
  } else {
    numth__svref(
      symval(q_ear_gf_powers),
      num_mod(
        num_mul(n, numth__svref(symval(q_d_gf_logs), gf_x2n(x))),
        numth__gf_ord(),
      ),
    )
  }
}

// ef coefficient arith for binary base fields:

///|
fn f2_red(a : Value) -> Value raise {
  let red = symval(q_ear_f2_red)
  let ilen = integer_length(red)
  let mut a = a
  while !numth__eqi(a, 0) {
    let e = integer_length(a) - ilen
    if e < 0 {
      return a
    }
    a = logxor(a, ash(red, e))
  }
  Fix(0L)
}

///|
fn f2_times(a : Value, b : Value) -> Value raise {
  let ilen = integer_length(b)
  let mut a1 = ash(a, ilen - 1)
  let mut ab = a1
  let mut i = ilen - 2
  let mut k = 0
  while i >= 0 {
    k -= 1
    if logbitp(i, b) {
      a1 = ash(a1, k)
      ab = logxor(ab, a1)
      k = 0
    }
    i -= 1
  }
  f2_red(ab)
}

///|
/// assume n >= 0
fn f2_pow(a : Value, n : Value) -> Value raise {
  if numth__eqi(n, 0) {
    Fix(1L)
  } else if numth__eqi(a, 0) {
    Fix(0L)
  } else {
    let mut a = a
    let mut n = n
    let mut res : Value = Nil
    while true {
      if oddp(n) {
        res = if res.truthy() { f2_times(a, res) } else { a }
        if numth__eqi(n, 1) {
          return res
        }
      }
      n = ash(n, -1)
      a = f2_times(a, a)
    }
    Nil
  }
}

///|
fn f2_inv(b : Value) -> Value raise {
  if numth__eqi(b, 0) {
    numth__err("f2 arithmetic: Quotient by zero", []) |> ignore
  }
  let mut b = b
  let mut b1 : Value = Fix(1L)
  let mut a = symval(q_ear_f2_red)
  let mut a1 : Value = Fix(0L)
  while !numth__eqi(b, 0) {
    let (q, r) = f2_divide(a, b)
    a = b
    b = r
    let ob1 = b1
    b1 = logxor(f2_times(q, ob1), a1)
    a1 = ob1
  }
  a1
}

///|
fn f2_divide(a : Value, b : Value) -> (Value, Value) raise {
  if numth__eqi(b, 0) {
    numth__err("f2 arithmetic: Quotient by zero", []) |> ignore
    (Nil, Nil)
  } else if numth__eqi(a, 0) {
    (Fix(0L), Fix(0L))
  } else {
    let ilen = integer_length(b)
    let mut q : Value = Fix(0L)
    let mut a = a
    while !numth__eqi(a, 0) {
      let e = integer_length(a) - ilen
      if e < 0 {
        return (q, a)
      }
      q = logxor(q, ash(Fix(1L), e))
      a = logxor(a, ash(b, e))
    }
    (q, Fix(0L))
  }
}

// setting the finite field and retrieving basic information ------------------

///|
/// deprecated
fn d_gf_set(
  p : Value,
  a1? : Value = Nil,
  a2? : Value = Nil,
  a3? : Value = Nil,
) -> Value raise {
  format(
    t,
    "`gf_set' is deprecated. ~%~\n             The user is asked to use `gf_set_data' instead.~%",
    [],
  )
  |> ignore
  if a2.truthy() {
    format(
      t,
      "In future versions `gf_set_data' will only accept two arguments.~%",
      [],
    )
    |> ignore
  }
  d_gf_set_data(p, a1~, a2~, a3~)
}

///|
/// opt: *gf-exp*, *gf-red*, *gf-fs-ord*
fn d_gf_set_data(
  p : Value,
  a1? : Value = Nil,
  a2? : Value = Nil,
  a3? : Value = Nil,
) -> Value raise {
  ignore(a2)
  ignore(a3) // remove a2 a3 in next versions
  numth__ef(Nil, fn() {
    if !(integerp(p) && primep(p).truthy()) {
      numth__err(
        "`gf_set_data': Field characteristic must be a prime number.",
        [],
      )
      |> ignore
    }
    d_gf_unset() |> ignore
    set(q_ear_gf_char, p) |> ignore
    if a1.truthy() {
      // exponent or reduction poly
      if integerp(a1) {
        if !(fixnump(a1) && plusp(a1)) {
          numth__err("`gf_set_data': The exponent must be a positive fixnum.", [])
          |> ignore
        }
        set(q_ear_gf_exp, a1) |> ignore
      } else {
        set(q_ear_gf_red, gf_p2x_red(a1, Str("gf_set_data"))) |> ignore
        set(q_ear_gf_exp, car(numth__gf_red())) |> ignore
        set(
          q_ear_gf_irred_q,
          gf_irr_p(numth__gf_red(), numth__gf_char(), symval(q_ear_gf_exp)),
        )
        |> ignore
      }
    }
    gf_set_rat_header() |> ignore // CRE-headers
    if numth__gf_red() is Nil {
      // find irreducible reduction poly:
      set(
        q_ear_gf_red,
        if numth__eqi(symval(q_ear_gf_exp), 1) {
          list2(Fix(1L), Fix(1L))
        } else {
          gf_irr(p, symval(q_ear_gf_exp))
        },
      )
      |> ignore
      set(q_ear_gf_irred_q, t) |> ignore
    }
    if numth__eqi(numth__gf_char(), 2) {
      set(q_ear_f2_red, gf_x2n(numth__gf_red())) |> ignore
    }
    let gf_exp = symval(q_ear_gf_exp)
    set(q_ear_gf_card, expt(p, gf_exp)) |> ignore // cardinality #(F)
    set(
      q_ear_gf_ord, // group order #(F*)
      if numth__eqi(gf_exp, 1) {
        one_minus(p)
      } else if !symval(q_ear_gf_irred_q).truthy() {
        gf_group_order(numth__gf_char(), numth__gf_red())
      } else {
        one_minus(expt(p, gf_exp))
      },
    )
    |> ignore
    numth__nofaclim(fn() {
      let fs = get_factor_list(numth__gf_ord())
      set(q_ear_gf_fs_ord, numth__sort_car(fs)) // .. [pi, ei] ..
    })
    |> ignore
    if symval(q_ear_gf_irred_q).truthy() {
      gf_precomp() |> ignore
    }
    set(
      q_ear_gf_prim, // primitive element
      if numth__eqi(gf_exp, 1) {
        if numth__eqi(numth__gf_char(), 2) {
          list2(Fix(0L), Fix(1L))
        } else {
          list2(
            Fix(0L),
            zn_primroot(
              p,
              numth__gf_ord(),
              mapcar(x => car(x), symval(q_ear_gf_fs_ord)),
            ),
          ) // .. pi ..  (factors_only:true)
        }
      } else if symval(q_ear_gf_irred_q).truthy() {
        gf_prim()
      } else {
        q_d_unknown
      },
    )
    |> ignore
    // global flags
    set(q_ear_gf_char_q, t) |> ignore
    set(q_ear_gf_red_q, t) |> ignore
    set(q_ear_gf_data_q, t) |> ignore
    d_gf_get_data() // data structure
  })
}

///|
fn gf_set_rat_header() -> Value raise {
  numth__with_modulus(Nil, fn() {
    set(q_ear_gf_rat_header, car(d_rat(q_d_x, Nil)))
  })
}

///|
fn gf_p2x_red(p : Value, fun : Value) -> Value raise {
  numth__with_modulus(Nil, fn() {
    let mut x = car(prep1(p))
    let ok = listp(x) &&
      {
        x = cdr(x)
        every(c => numberp(c), x)
      }
    if !ok {
      numth__err("`~m': Not suitable as reduction polynomial: ~m", [fun, p])
      |> ignore
    }
    x = gf_mod(x)
    if !(fixnump(car(x)) && plusp(car(x))) {
      numth__err("`~m': The exponent must be a positive fixnum.", [fun])
      |> ignore
    }
    if !eql(Fix(1L), cadr(x)) {
      numth__err("`~m': A monic reduction polynomial is assumed.", [fun])
      |> ignore
    }
    x
  })
}

///|
fn d_ef_set_data(red : Value) -> Value raise {
  ef_gf_field_q(Str("ef_set_data")) |> ignore
  d_ef_unset() |> ignore
  numth__ef(t, fn() {
    set(q_ear_ef_red, gf_p2x_red(red, Str("ef_set_data"))) |> ignore
    set(q_ear_ef_exp, car(numth__ef_red())) |> ignore
    set(q_ear_ef_card, expt(numth__gf_card(), symval(q_ear_ef_exp))) |> ignore
    set(
      q_ear_ef_irred_q,
      gf_irr_p(numth__ef_red(), numth__gf_card(), symval(q_ear_ef_exp)),
    )
    |> ignore
    set(
      q_ear_ef_ord,
      if symval(q_ear_ef_irred_q).truthy() {
        one_minus(symval(q_ear_ef_card))
      } else {
        gf_group_order(numth__gf_card(), numth__ef_red())
      },
    )
    |> ignore
    numth__nofaclim(fn() {
      let fs = get_factor_list(symval(q_ear_ef_ord))
      set(q_ear_ef_fs_ord, numth__sort_car(fs))
    })
    |> ignore
    if symval(q_ear_ef_irred_q).truthy() {
      ef_precomp() |> ignore
    }
    set(q_ear_ef_data_q, t) |> ignore
    set(q_ear_ef_red_q, t) |> ignore
    set(
      q_ear_ef_prim,
      if numth__eqi(symval(q_ear_ef_exp), 1) {
        list2(
          Fix(0L),
          numth__ef(Nil, fn() { gf_x2n(symval(q_ear_gf_prim)) }),
        )
      } else if symval(q_ear_ef_irred_q).truthy() {
        ef_prim()
      } else {
        q_d_unknown
      },
    )
    |> ignore
  })
  d_ef_get_data()
}

///|
/// (defstruct (gf-data (:print-function gf-data-short-print))
///   char exp red prim card ord fs-ord fsx fsx-base-p x^p-powers )
fn gf_data_short_print(struct_ : Value, stream : Value, i : Value) -> Value raise {
  ignore(struct_)
  ignore(i)
  format(stream, "Structure [GF-DATA]", []) // wxMaxima returns this
  // terminal should return this too
}

///|
/// returns a struct containing all data necessary to use gf_set_again
fn d_gf_get_data() -> Value raise {
  gf_data_q(Str("gf_get_data")) |> ignore
  make_struct("gf-data", [
    symval(q_ear_gf_char), // characteristic
    symval(q_ear_gf_exp), // exponent
    symval(q_ear_gf_red), // reduction
    symval(q_ear_gf_prim), // primitive
    symval(q_ear_gf_card), // cardinality
    symval(q_ear_gf_ord), // order
    symval(q_ear_gf_fs_ord), // factors of order
    symval(q_ear_gf_fsx), // extended factors of order
    symval(q_ear_gf_fsx_base_p), // extended factors in base p
    symval(q_ear_gf_x_hatp_powers), // pre-calculated powers
  ])
}

///|
/// (defstruct (ef-data (:print-function ef-data-short-print))
///   exp red prim card ord fs-ord fsx fsx-base-q x^q-powers )
fn ef_data_short_print(struct_ : Value, stream : Value, i : Value) -> Value raise {
  ignore(struct_)
  ignore(i)
  format(stream, "Structure [EF-DATA]", [])
}

///|
fn d_ef_get_data() -> Value raise {
  ef_data_q(Str("ef_get_data")) |> ignore
  make_struct("ef-data", [
    symval(q_ear_ef_exp), // exponent
    symval(q_ear_ef_red), // reduction
    symval(q_ear_ef_prim), // primitive
    symval(q_ear_ef_card), // cardinality
    symval(q_ear_ef_ord), // order
    symval(q_ear_ef_fs_ord), // factors of order
    symval(q_ear_ef_fsx), // extended factors of order
    symval(q_ear_ef_fsx_base_q), // extended factors in base q
    symval(q_ear_ef_x_hatq_powers), // pre-calculated powers
  ])
}

///|
fn d_gf_info(t_q? : Value = t) -> Value raise {
  gf_data_q(Str("gf_info")) |> ignore
  let prim = symval(q_ear_gf_prim)
  let no_prim = prim is Nil || equal(prim, q_d_unknown)
  numth__ef(Nil, fn() {
    let a1 = numth__gf_char()
    let a2 = mfuncall(q_d_string, list1(gf_x2p(numth__gf_red())))
    let a3 = mfuncall(
      q_d_string,
      list1(
        if no_prim {
          symval(q_ear_gf_prim)
        } else {
          gf_x2p(symval(q_ear_gf_prim))
        },
      ),
    )
    let a4 = numth__gf_card()
    let a5 = numth__gf_ord()
    let a6 = totient_by_fs_n(symval(q_ear_gf_fs_ord))
    format(
      t_q,
      "characteristic = ~a~:[, ~;~%~]~\n       reduction polynomial = ~a~:[, ~;~%~]~\n       primitive element = ~a~:[, ~;~%~]~\n       nr of elements = ~a~:[, ~;~%~]~\n       nr of units = ~a~:[, ~;~]~\n       ~:[~;~%nr of primitive elements = ~a~] ~%",
      [
        a1,
        t_q,
        a2,
        t_q,
        a3,
        t_q,
        a4,
        t_q,
        a5,
        lbool(t_q.truthy() || no_prim),
        lbool(!no_prim),
        a6,
      ],
    )
  })
}

///|
fn totient_by_fs_n(fs_n : Value) -> Value raise {
  let mut phi : Value = Fix(1L)
  for f in fs_n.iter() {
    let p = car(f)
    let e = cadr(f)
    phi = num_mul(phi, num_mul(one_minus(p), expt(p, one_minus(e))))
  }
  phi
}

///|
/// enables testing gf_set_data in rtest
fn d_gf_infolist() -> Value raise {
  gf_data_q(Str("gf_infolist")) |> ignore
  numth__ef(Nil, fn() {
    let prim = symval(q_ear_gf_prim)
    list([
      numth__mlist(),
      numth__gf_char(),
      gf_x2p(numth__gf_red()),
      if prim is Nil || equal(prim, q_d_unknown) {
        prim
      } else {
        gf_x2p(prim)
      },
      numth__gf_card(),
      numth__gf_ord(),
    ])
  })
}

///|
fn d_ef_info(t_q? : Value = t) -> Value raise {
  ef_data_q(Str("ef_info")) |> ignore
  let prim = symval(q_ear_ef_prim)
  let no_prim = prim is Nil || equal(prim, q_d_unknown)
  numth__ef(t, fn() {
    let a1 = mfuncall(q_d_string, list1(gf_x2p(numth__ef_red())))
    let a2 = mfuncall(
      q_d_string,
      list1(
        if no_prim {
          symval(q_ear_ef_prim)
        } else {
          gf_x2p(symval(q_ear_ef_prim))
        },
      ),
    )
    let a3 = symval(q_ear_ef_card)
    let a4 = symval(q_ear_ef_ord)
    let a5 = totient_by_fs_n(symval(q_ear_ef_fs_ord))
    format(
      t_q,
      "reduction polynomial = ~a~:[, ~;~%~]~\n       primitive element = ~a~:[, ~;~%~]~\n       nr of elements = ~a~:[, ~;~%~]~\n       nr of units = ~a~:[, ~;~]~\n       ~:[~;~%nr of primitive elements = ~a~] ~%",
      [
        a1,
        t_q,
        a2,
        t_q,
        a3,
        t_q,
        a4,
        lbool(t_q.truthy() || no_prim),
        lbool(!no_prim),
        a5,
      ],
    )
  })
}

///|
/// enables testing ef_set_data in rtest
fn d_ef_infolist() -> Value raise {
  ef_data_q(Str("ef_infolist")) |> ignore
  numth__ef(t, fn() {
    let prim = symval(q_ear_ef_prim)
    list([
      numth__mlist(),
      gf_x2p(numth__ef_red()),
      if prim is Nil || equal(prim, q_d_unknown) {
        prim
      } else {
        gf_x2p(prim)
      },
      symval(q_ear_ef_card),
      symval(q_ear_ef_ord),
    ])
  })
}

///|
fn d_gf_unset() -> Value raise {
  set(q_d_gf_powers, Nil) |> ignore
  set(q_d_gf_logs, Nil) |> ignore
  set(q_d_gf_zech_logs, Nil) |> ignore
  set(q_ear_gf_powers, Nil) |> ignore
  set(q_ear_gf_logs_q, Nil) |> ignore
  set(q_d_gf_rat, Nil) |> ignore
  set(q_d_ef_coeff_mult, Nil) |> ignore
  set(q_d_ef_coeff_add, Nil) |> ignore
  set(q_d_ef_coeff_inv, Nil) |> ignore
  set(q_d_ef_coeff_exp, Nil) |> ignore
  set(q_ear_gf_rat_header, Nil) |> ignore
  set(q_ear_gf_char, Fix(0L)) |> ignore
  set(q_ear_gf_exp, Fix(1L)) |> ignore // *gf-exp* = 1 when gf_set_data has no optional arg
  set(q_ear_gf_ord, Fix(0L)) |> ignore
  set(q_ear_gf_card, Fix(0L)) |> ignore
  set(q_ear_gf_red, Nil) |> ignore
  set(q_ear_f2_red, Fix(0L)) |> ignore
  set(q_ear_gf_prim, Nil) |> ignore
  set(q_ear_gf_fs_ord, Nil) |> ignore
  set(q_ear_gf_fsx, Nil) |> ignore
  set(q_ear_gf_fsx_base_p, Nil) |> ignore
  set(q_ear_gf_x_hatp_powers, Nil) |> ignore
  set(q_ear_gf_char_q, Nil) |> ignore
  set(q_ear_gf_red_q, Nil) |> ignore
  set(q_ear_gf_irred_q, Nil) |> ignore
  set(q_ear_gf_data_q, Nil) |> ignore
  t
}

///|
fn d_ef_unset() -> Value raise {
  set(q_ear_ef_exp, Fix(0L)) |> ignore
  set(q_ear_ef_ord, Fix(0L)) |> ignore
  set(q_ear_ef_card, Fix(0L)) |> ignore
  set(q_ear_ef_red, Nil) |> ignore
  set(q_ear_ef_prim, Nil) |> ignore
  set(q_ear_ef_fs_ord, Nil) |> ignore
  set(q_ear_ef_fsx, Nil) |> ignore
  set(q_ear_ef_fsx_base_q, Nil) |> ignore
  set(q_ear_ef_x_hatq_powers, Nil) |> ignore
  set(q_ear_ef_red_q, Nil) |> ignore
  set(q_ear_ef_irred_q, Nil) |> ignore
  set(q_ear_ef_data_q, Nil) |> ignore
  t
}

///|
/// Minimal set
/// Just set characteristic and reduction poly to allow basic arithmetics on
/// the fly.
fn d_gf_minimal_set(p : Value, red? : Value = Nil) -> Value raise {
  if !(integerp(p) && primep(p).truthy()) {
    numth__err(
      "First argument to `gf_minimal_set' must be a prime number.",
      [],
    )
    |> ignore
  }
  d_gf_unset() |> ignore
  set(q_ear_gf_char, p) |> ignore
  set(q_ear_gf_char_q, t) |> ignore
  gf_set_rat_header() |> ignore
  numth__ef(Nil, fn() {
    if red.truthy() {
      set(q_ear_gf_red, gf_p2x_red(red, Str("gf_minimal_set"))) |> ignore
      set(q_ear_gf_red_q, t) |> ignore
      set(q_ear_gf_exp, car(numth__gf_red())) |> ignore
    }
    format(Nil, "characteristic = ~a, reduction polynomial = ~a", [
      numth__gf_char(),
      if red.truthy() {
        mfuncall(q_d_string, list1(gf_x2p(numth__gf_red())))
      } else {
        Str("false")
      },
    ])
  })
}

///|
fn d_ef_minimal_set(red : Value) -> Value raise {
  ef_gf_field_q(Str("ef_minimal_set")) |> ignore
  d_ef_unset() |> ignore
  numth__ef(t, fn() {
    if red.truthy() {
      set(q_ear_ef_red, gf_p2x_red(red, Str("ef_minimal_set"))) |> ignore
      set(q_ear_ef_exp, car(numth__ef_red())) |> ignore
      set(q_ear_ef_red_q, t) |> ignore
    }
    format(Nil, "reduction polynomial = ~a", [
      if red.truthy() {
        mfuncall(q_d_string, list1(gf_x2p(numth__ef_red())))
      } else {
        Str("false")
      },
    ])
  })
}

///|
fn d_gf_characteristic() -> Value raise {
  gf_char_q(Str("gf_characteristic")) |> ignore
  numth__gf_char()
}

///|
fn d_gf_exponent() -> Value raise {
  gf_red_q(Str("gf_exponent")) |> ignore
  symval(q_ear_gf_exp)
}

///|
fn d_gf_reduction() -> Value raise {
  gf_red_q(Str("gf_reduction")) |> ignore
  if numth__gf_red().truthy() {
    numth__ef(Nil, fn() { gf_x2p(numth__gf_red()) })
  } else {
    Nil
  }
}

///|
fn d_gf_cardinality() -> Value raise {
  gf_data_q(Str("gf_cardinality")) |> ignore
  numth__gf_card()
}

///|
fn d_ef_exponent() -> Value raise {
  ef_red_q(Str("ef_exponent")) |> ignore
  symval(q_ear_ef_exp)
}

///|
fn d_ef_reduction() -> Value raise {
  ef_red_q(Str("ef_reduction")) |> ignore
  if numth__ef_red().truthy() {
    numth__ef(t, fn() { gf_x2p(numth__ef_red()) })
  } else {
    Nil
  }
}

///|
fn d_ef_cardinality() -> Value raise {
  ef_data_q(Str("ef_cardinality")) |> ignore
  symval(q_ear_ef_card)
}

///|
/// Reuse data and results from a previous gf_set_data
fn d_gf_set_again(data : Value) -> Value raise {
  if !struct_typep(data, "gf-data") {
    numth__err(
      "Argument to `gf_set_again' must be a return value of `gf_set_data'.",
      [],
    )
    |> ignore
  }
  d_gf_unset() |> ignore
  gf_set_rat_header() |> ignore
  set(q_ear_gf_char, struct_ref(data, 0)) |> ignore
  set(q_ear_gf_exp, struct_ref(data, 1)) |> ignore
  set(q_ear_gf_red, struct_ref(data, 2)) |> ignore
  set(q_ear_gf_prim, struct_ref(data, 3)) |> ignore
  set(q_ear_gf_card, struct_ref(data, 4)) |> ignore
  set(q_ear_gf_ord, struct_ref(data, 5)) |> ignore
  set(q_ear_gf_fs_ord, struct_ref(data, 6)) |> ignore
  set(q_ear_gf_fsx, struct_ref(data, 7)) |> ignore
  set(q_ear_gf_fsx_base_p, struct_ref(data, 8)) |> ignore
  set(q_ear_gf_x_hatp_powers, struct_ref(data, 9)) |> ignore
  set(
    q_ear_gf_irred_q,
    lbool(num_eq(numth__gf_ord(), one_minus(numth__gf_card()))),
  )
  |> ignore
  set(q_ear_gf_char_q, t) |> ignore
  set(q_ear_gf_red_q, t) |> ignore
  set(q_ear_gf_data_q, t)
}

///|
fn d_ef_set_again(data : Value) -> Value raise {
  ef_gf_field_q(Str("ef_set_again")) |> ignore
  if !struct_typep(data, "ef-data") {
    numth__err(
      "Argument to `ef_set_again' must be a return value of `ef_set_data'.",
      [],
    )
    |> ignore
  }
  d_ef_unset() |> ignore
  set(q_ear_ef_exp, struct_ref(data, 0)) |> ignore
  set(q_ear_ef_red, struct_ref(data, 1)) |> ignore
  set(q_ear_ef_prim, struct_ref(data, 2)) |> ignore
  set(q_ear_ef_card, struct_ref(data, 3)) |> ignore
  set(q_ear_ef_ord, struct_ref(data, 4)) |> ignore
  set(q_ear_ef_fs_ord, struct_ref(data, 5)) |> ignore
  set(q_ear_ef_fsx, struct_ref(data, 6)) |> ignore
  set(q_ear_ef_fsx_base_q, struct_ref(data, 7)) |> ignore
  set(q_ear_ef_x_hatq_powers, struct_ref(data, 8)) |> ignore
  set(
    q_ear_ef_irred_q,
    lbool(num_eq(symval(q_ear_ef_ord), one_minus(symval(q_ear_ef_card)))),
  )
  |> ignore
  set(q_ear_ef_red_q, t) |> ignore
  set(q_ear_ef_data_q, t)
}

// lookup tables ---------------------------------------------------------------

///|
fn d_gf_make_arrays() -> Value raise {
  format(
    t,
    "`gf_make_arrays' is deprecated. ~%~\n             The user is asked to use `gf_make_logs' instead.~%",
    [],
  )
  |> ignore
  d_gf_make_logs()
}

///|
/// also zech-logs and antilogs
fn d_gf_make_logs() -> Value raise {
  gf_field_q(Str("gf_make_logs")) |> ignore
  numth__ef(Nil, fn() { gf_make_logs() })
}

///|
fn gf_make_logs() -> Value raise {
  if !fixnump(numth__gf_ord()) {
    numth__err("`gf_make_logs': group order must be a fixnum.", []) |> ignore
  }
  let mut x = list2(Fix(0L), Fix(1L))
  let ord = to_int(numth__gf_ord())
  let primx = symval(q_ear_gf_prim)
  let red = numth__gf_red()
  //
  // power table of the field, where the i-th element is (the numerical
  // equivalent of) the field element e^i, where e is a primitive element
  //
  let powers = make_array([ord + 1], elt="integer")
  set(q_d_gf_powers, powers) |> ignore
  let xpowers = make_array([ord + 1], initial=Nil, elt="list")
  set(q_ear_gf_powers, xpowers) |> ignore
  aset1(powers, 0, Fix(1L)) |> ignore
  aset1(xpowers, 0, list2(Fix(0L), Fix(1L))) |> ignore
  for i in 1..=ord {
    x = gf_times(x, primx, red)
    aset1(powers, i, gf_x2n(x)) |> ignore
    aset1(xpowers, i, x) |> ignore
  }
  //
  // log table: the inverse lookup of the power table
  //
  let logs = make_array([ord + 1], initial=Nil)
  set(q_d_gf_logs, logs) |> ignore
  for i in 0..<ord {
    aset1(logs, to_int(aref1(powers, i)), numth__i(i)) |> ignore
  }
  //
  // zech-log table: lookup table for efficient addition
  //
  let zech = make_array([ord + 1], initial=Nil)
  set(q_d_gf_zech_logs, zech) |> ignore
  let one = list2(Fix(0L), Fix(1L))
  for i in 0..=ord {
    aset1(
      zech,
      i,
      numth__svref(logs, gf_x2n(gf_plus(aref1(xpowers, i), one))),
    )
    |> ignore
  }
  //
  set(q_ear_gf_logs_q, t) |> ignore
  list([numth__mlist(), powers, logs, zech])
}

///|
fn gf_clear_tables() -> Value raise {
  set(q_d_gf_powers, Nil) |> ignore
  set(q_d_gf_logs, Nil) |> ignore
  set(q_d_gf_zech_logs, Nil) |> ignore
  set(q_ear_gf_logs_q, Nil)
}

// converting to/from internal representation ----------------------------------
//
// user level      <---> internal
// 0                     nil
// integer # 0           (0 integer') where integer' = mod(integer, *gf-char*)
// x                     (1 1)
// x^4 + 3*x^2 + 4       (4 1 2 3 0 4)
//
// This representation uses the term part of the internal CRE
// representation.  The coefficients are exclusively positive: 1, 2, ...,
// (*gf-char* -1).  Header information is stored in *gf-rat-header*.

///|
fn gf_p2x(p : Value) -> Value raise {
  let p = car(numth__with_modulus(Nil, fn() { prep1(p) }))
  if integerp(p) {
    if numth__eqi(p, 0) {
      Nil
    } else {
      let p = gf_cmod(p)
      if numth__eqi(p, 0) {
        Nil
      } else {
        list2(Fix(0L), p)
      }
    }
  } else {
    let p = gf_mod(cdr(p))
    if fixnump(car(p)) {
      p
    } else {
      numth__err("Exponents are limited to fixnums.", [])
    }
  }
}

///|
/// version of gf-p2x that doesn't apply mod reduction
fn gf_p2x_raw(p : Value) -> Value raise {
  let p = car(numth__with_modulus(Nil, fn() { prep1(p) }))
  if integerp(p) {
    if numth__eqi(p, 0) {
      Nil
    } else {
      list2(Fix(0L), p)
    }
  } else {
    let p = cdr(p)
    if !every(c => numberp(c), p) {
      numth__err("gf: polynomials must be univariate.", []) |> ignore
    }
    p
  }
}

///|
fn gf_x2p(x : Value) -> Value raise {
  let x : Value = if x is Nil {
    Fix(0L)
  } else if numth__eqi(car(x), 0) {
    gf_cp2smod(cadr(x))
  } else {
    gf_np2smod(x)
  }
  if eql(symval(q_d_gf_rat), t) {
    gf_x2cre(x)
  } else {
    gf_disrep(x)
  }
}

///|
/// depending on $gf_rat gf-x2p returns a CRE or a ratdisrepped expression
fn gf_x2cre(x : Value) -> Value raise {
  let header = symval(q_ear_gf_rat_header)
  if integerp(x) {
    cons(header, cons(x, Fix(1L)))
  } else {
    cons(header, cons(cons(caar(cdddr(header)), x), Fix(1L)))
  }
}

///|
fn gf_disrep(x : Value, var_? : Value = q_d_x) -> Value raise {
  if integerp(x) {
    return x
  }
  let v = var_
  let mut x = x
  let not_plus = cddr(x) is Nil
  let mut p : Value = Nil
  while x is Cons(_) {
    let e = car(x)
    let c = cadr(x)
    x = cddr(x)
    p = if numth__eqi(e, 0) {
      cons(c, p)
    } else if numth__eqi(e, 1) {
      if numth__eqi(c, 1) {
        cons(v, p)
      } else {
        cons(list3(list2(q_mtimes, q_simp), c, v), p)
      }
    } else if numth__eqi(c, 1) {
      cons(list3(list2(q_mexpt, q_simp), v, e), p)
    } else {
      cons(
        list3(
          list2(q_mtimes, q_simp),
          c,
          list3(list2(q_mexpt, q_simp), v, e),
        ),
        p,
      )
    }
  }
  if not_plus {
    car(p)
  } else {
    cons(list2(q_mplus, q_simp), p)
  }
}

// evaluation and adjustment ---------------------------------------------------

///|
/// an arbitrary polynomial is evaluated in a given field
fn d_gf_eval(a : Value) -> Value raise {
  gf_char_q(Str("gf_eval")) |> ignore
  numth__ef(Nil, fn() { gf_eval(a, numth__gf_red(), Str("gf_eval")) })
}

///|
fn d_ef_eval(a : Value) -> Value raise {
  ef_gf_field_q(Str("ef_eval")) |> ignore
  numth__ef(t, fn() {
    if !equal(a, d_expand(a)) {
      numth__err(
        "`ef_eval': The argument must be an expanded polynomial.",
        [],
      )
      |> ignore
    }
    gf_eval(a, numth__ef_red(), Str("ef_eval"))
  })
}

///|
fn gf_eval(a : Value, red : Value, fun : Value) -> Value raise {
  let a = numth__with_modulus(Nil, fn() { car(prep1(a)) })
  if integerp(a) {
    gf_cmod(a)
  } else {
    let a = gf_mod(cdr(a))
    if a.truthy() && !fixnump(car(a)) {
      numth__err("`~m': The exponent is expected to be a fixnum.", [fun])
      |> ignore
    }
    gf_x2p(gf_nred(a, red))
  }
}

///|
/// gf-mod adjusts arbitrary integer coefficients (pos, neg or unbounded)
fn gf_mod(x : Value) -> Value raise {
  if x is Nil {
    return Nil
  }
  let mut r = x
  let mut res : Value = Nil
  while r is Cons(_) {
    if !numberp(cadr(r)) {
      numth__err("gf: polynomials must be univariate.", []) |> ignore
    }
    let c = gf_cmod(cadr(r))
    if !numth__eqi(c, 0) {
      res = cons(c, cons(car(r), res))
    }
    r = cddr(r)
  }
  nreverse(res)
}

///|
/// positive 2 symmetric mod (modifies x)
fn gf_np2smod(x : Value) -> Value raise {
  if x is Nil {
    Nil
  } else if !symval(q_d_gf_balanced).truthy() {
    x
  } else if numth__efp() {
    n_starf_np2smod(
      x,
      numth__gf_card(),
      lfunc("gf-np2smod-ef", args => neg(
        gf_ctimes(one_minus(numth__gf_char()), args[0]),
      )),
    )
  } else {
    n_starf_np2smod(
      x,
      numth__gf_char(),
      lfunc("gf-np2smod", args => num_sub(args[0], numth__gf_char())),
    )
  }
}

///|
fn n_starf_np2smod(x : Value, p : Value, cp2smod_fn : Value) -> Value raise {
  if x is Nil {
    return x
  }
  let p2 = ash(p, -1)
  let mut r = cdr(x)
  while true {
    if num_gt(car(r), p2) {
      rplaca(r, funcall(cp2smod_fn, [car(r)])) |> ignore
    }
    if cdr(r) is Nil {
      return x
    }
    r = cddr(r)
  }
  x
}

///|
/// adjust a coefficient to a symmetric modulus:
fn gf_cp2smod(c : Value) -> Value raise {
  if !symval(q_d_gf_balanced).truthy() {
    c
  } else if numth__efp() {
    if num_gt(c, ash(numth__gf_card(), -1)) {
      neg(gf_ctimes(c, one_minus(numth__gf_char())))
    } else {
      c
    }
  } else if num_gt(c, ash(numth__gf_char(), -1)) {
    num_sub(c, numth__gf_char())
  } else {
    c
  }
}

// arithmetic in Galois Fields - Maxima level functions ------------------------

// gf:

///|
fn d_gf_neg(a : Value) -> Value raise {
  gf_char_q(Str("gf_neg")) |> ignore
  numth__ef(Nil, fn() { gf_x2p(gf_nminus(gf_p2x(a))) })
}

///|
fn d_gf_add(args : Value) -> Value raise {
  gf_char_q(Str("gf_add")) |> ignore
  numth__ef(Nil, fn() {
    let args = mapcar(x => gf_p2x(x), args)
    gf_x2p(reduce((x, y) => gf_plus(x, y), args))
  })
}

///|
fn d_gf_sub(args : Value) -> Value raise {
  gf_char_q(Str("gf_sub")) |> ignore
  numth__ef(Nil, fn() {
    let args = mapcar(x => gf_p2x(x), args)
    gf_x2p(
      gf_plus(car(args), gf_minus(reduce((x, y) => gf_plus(x, y), cdr(args)))),
    )
  })
}

///|
/// `(not (typep (apply #'+ (mapcar #'car args)) 'fixnum))`
fn numth__exps_not_fixnum(args : Value) -> Bool raise {
  let mut s : Value = Fix(0L)
  for x in args.iter() {
    s = num_add(s, car(x))
  }
  !fixnump(s)
}

///|
fn d_gf_mult(args : Value) -> Value raise {
  gf_char_q(Str("gf_mult")) |> ignore
  numth__ef(Nil, fn() {
    let args = mapcar(x => gf_p2x(x), args)
    if numth__gf_red() is Nil &&
      !some(x => x is Nil, args) &&
      numth__exps_not_fixnum(args) {
      numth__err("`gf_mult': Resulting exponent won't be a fixnum.", [])
      |> ignore
    }
    gf_x2p(reduce((x, y) => gf_times(x, y, numth__gf_red()), args))
  })
}

///|
fn d_gf_reduce(a : Value, b : Value) -> Value raise {
  gf_char_q(Str("gf_reduce")) |> ignore
  numth__ef(Nil, fn() { gf_x2p(gf_nrem(gf_p2x(a), gf_p2x(b))) })
}

///|
fn d_gf_inv(a : Value) -> Value raise {
  gf_red_q(Str("gf_inv")) |> ignore
  numth__ef(Nil, fn() {
    let a = gf_inv(gf_p2x(a), numth__gf_red())
    if a.truthy() {
      gf_x2p(a)
    } else {
      Nil
    } // a is nil in case the inverse does not exist
  })
}

///|
fn d_gf_div(args : Value) -> Value raise {
  gf_red_q(Str("gf_div")) |> ignore
  if cadr(args) is Nil {
    numth__err("`gf_div' needs at least two arguments.", []) |> ignore
  }
  numth__ef(Nil, fn() {
    let a2 = mapcar(x => gf_p2x(x), args)
    let a2 = cons(car(a2), mapcar(x => gf_inv(x, numth__gf_red()), cdr(a2)))
    if some(x => x is Nil, cdr(a2)) {
      // but check if exact division is possible ..
      let mut q = gf_p2x(car(args))
      let mut args = cdr(args)
      while true {
        let d = car(args)
        if d is Nil {
          return gf_x2p(q)
        }
        let (q1, r) = gf_divide(q, gf_p2x(d))
        q = q1
        if r.truthy() {
          return Nil // .. in case it is not return false
        }
        args = cdr(args)
      }
      Nil
    } else {
      // a / b = a * b^-1 :
      gf_x2p(reduce((x, y) => gf_times(x, y, numth__gf_red()), a2))
    }
  })
}

///|
fn d_gf_exp(a : Value, n : Value) -> Value raise {
  gf_char_q(Str("gf_exp")) |> ignore
  numth__ef(Nil, fn() {
    if n is Nil {
      numth__err("`gf_exp' needs two arguments.", [])
    } else if !integerp(n) {
      numth__err("Second argument to `gf_exp' must be an integer.", [])
    } else if minusp(n) {
      if numth__gf_red() is Nil {
        numth__err("`gf_exp': Unknown reduction polynomial.", []) |> ignore
      }
      let a = gf_inv(gf_p2x(a), numth__gf_red())
      if a.truthy() {
        d_gf_exp(gf_x2p(a), neg(n))
      } else {
        Nil
      } // a is nil in case the inverse does not exist
    } else if symval(q_ear_gf_logs_q).truthy() {
      gf_x2p(gf_pow_by_table(gf_p2x(a), n))
    } else if symval(q_ear_gf_irred_q).truthy() &&
      symval(q_ear_gf_x_hatp_powers).truthy() {
      gf_x2p(gf_pow_dol(gf_p2x(a), n, numth__gf_red()))
    } else {
      let a = gf_p2x(a)
      if numth__gf_red() is Nil &&
        a.truthy() &&
        !fixnump(num_mul(n, car(a))) {
        numth__err("`gf_exp': Resulting exponent won't be a fixnum.", [])
        |> ignore
      }
      gf_x2p(gf_pow(a, n, numth__gf_red()))
    }
  })
}

// ef:

///|
fn d_ef_neg(a : Value) -> Value raise {
  ef_gf_field_q(Str("ef_neg")) |> ignore
  numth__ef(t, fn() { gf_x2p(gf_nminus(gf_p2x(a))) })
}

///|
fn d_ef_add(args : Value) -> Value raise {
  ef_gf_field_q(Str("ef_add")) |> ignore
  numth__ef(t, fn() {
    let args = mapcar(x => gf_p2x(x), args)
    gf_x2p(reduce((x, y) => gf_plus(x, y), args))
  })
}

///|
fn d_ef_sub(args : Value) -> Value raise {
  ef_gf_field_q(Str("ef_sub")) |> ignore
  numth__ef(t, fn() {
    let args = mapcar(x => gf_p2x(x), args)
    gf_x2p(
      gf_plus(car(args), gf_minus(reduce((x, y) => gf_plus(x, y), cdr(args)))),
    )
  })
}

///|
fn d_ef_mult(args : Value) -> Value raise {
  ef_gf_field_q(Str("ef_mult")) |> ignore
  numth__ef(t, fn() {
    let red = numth__ef_red()
    let args = mapcar(x => gf_p2x(x), args)
    if red is Nil && !some(x => x is Nil, args) && numth__exps_not_fixnum(args) {
      numth__err("`ef_mult': Resulting exponent won't be a fixnum.", [])
      |> ignore
    }
    gf_x2p(reduce((x, y) => gf_times(x, y, red), args))
  })
}

///|
fn d_ef_reduce(a : Value, b : Value) -> Value raise {
  ef_gf_field_q(Str("ef_reduce")) |> ignore
  numth__ef(t, fn() { gf_x2p(gf_nrem(gf_p2x(a), gf_p2x(b))) })
}

///|
fn d_ef_inv(a : Value) -> Value raise {
  ef_red_q(Str("ef_inv")) |> ignore
  numth__ef(t, fn() {
    let a = gf_inv(gf_p2x(a), numth__ef_red())
    if a.truthy() {
      gf_x2p(a)
    } else {
      Nil
    }
  })
}

///|
fn d_ef_div(args : Value) -> Value raise {
  ef_red_q(Str("ef_div")) |> ignore
  if cadr(args) is Nil {
    numth__err("`ef_div' needs at least two arguments.", []) |> ignore
  }
  numth__ef(t, fn() {
    let red = numth__ef_red()
    let args = mapcar(x => gf_p2x(x), args)
    let args = cons(car(args), mapcar(x => gf_inv(x, red), cdr(args)))
    if car(args) is Nil {
      Fix(0L)
    } else if some(x => x is Nil, cdr(args)) {
      Nil
    } else {
      gf_x2p(reduce((x, y) => gf_times(x, y, red), args))
    }
  })
}

///|
fn d_ef_exp(a : Value, n : Value) -> Value raise {
  ef_gf_field_q(Str("ef_exp")) |> ignore
  numth__ef(t, fn() {
    if minusp(n) {
      if numth__ef_red() is Nil {
        numth__err("`ef_exp': Unknown reduction polynomial.", []) |> ignore
      }
      let a = gf_inv(gf_p2x(a), numth__ef_red())
      if a.truthy() {
        d_ef_exp(gf_x2p(a), neg(n))
      } else {
        Nil
      }
    } else if symval(q_ear_ef_irred_q).truthy() &&
      symval(q_ear_ef_x_hatq_powers).truthy() {
      gf_x2p(gf_pow_dol(gf_p2x(a), n, numth__ef_red()))
    } else {
      let a = gf_p2x(a)
      if numth__ef_red() is Nil &&
        a.truthy() &&
        !fixnump(num_mul(n, car(a))) {
        numth__err("`ef_exp': Resulting exponent won't be a fixnum.", [])
        |> ignore
      }
      gf_x2p(gf_pow(a, n, numth__ef_red()))
    }
  })
}

// arithmetic in Galois Fields - Lisp level functions --------------------------
//
// Both gf (base field) and ef (extension field) Maxima level functions use
// this Lisp level functions. The switch *ef-arith?* controls how the
// coefficients were treated. The coefficient functions gf-ctimes and friends
// behave differently depending on *ef-arith?*.
//
// Remark: A prefixed character 'n' indicates a destructive function.

///|
/// c * x
fn gf_xctimes(x : Value, c : Value) -> Value raise {
  if numth__eqi(c, 0) || x is Nil {
    return Nil
  }
  let res = list2(car(x), gf_ctimes(c, cadr(x)))
  let mut r = cdr(res)
  let mut rx = cddr(x)
  while rx is Cons(_) {
    rplacd(r, list2(car(rx), gf_ctimes(c, cadr(rx)))) |> ignore
    r = cddr(r)
    rx = cddr(rx)
  }
  res
}

///|
/// modifies x
fn gf_nxctimes(x : Value, c : Value) -> Value raise {
  if numth__eqi(c, 0) || x is Nil {
    return Nil
  }
  let mut r = cdr(x)
  while r is Cons(_) {
    rplaca(r, gf_ctimes(c, car(r))) |> ignore
    r = cddr(r)
  }
  x
}

///|
/// c*v^e * x
fn gf_xectimes(x : Value, e : Value, c : Value) -> Value raise {
  if numth__eqi(c, 0) || x is Nil {
    return Nil
  }
  let res = list2(num_add(e, car(x)), gf_ctimes(c, cadr(x)))
  let mut r = cdr(res)
  let mut rx = cddr(x)
  while rx is Cons(_) {
    rplacd(r, list2(num_add(e, car(rx)), gf_ctimes(c, cadr(rx)))) |> ignore
    r = cddr(r)
    rx = cddr(rx)
  }
  res
}

///|
/// v^e * x (modifies x)
fn gf_nxetimes(x : Value, e : Value) -> Value raise {
  if x is Nil {
    return x
  }
  let mut r = x
  while r is Cons(_) {
    rplaca(r, num_add(e, car(r))) |> ignore
    r = cddr(r)
  }
  x
}

///|
/// - x
fn gf_minus(x : Value) -> Value raise {
  if x is Nil || numth__eqi(numth__gf_char(), 2) {
    return x
  }
  let res = list2(car(x), gf_cminus_b(cadr(x)))
  let mut r = cdr(res)
  let mut rx = cddr(x)
  while rx is Cons(_) {
    rplacd(r, list2(car(rx), gf_cminus_b(cadr(rx)))) |> ignore
    r = cddr(r)
    rx = cddr(rx)
  }
  res
}

///|
/// modifies x
fn gf_nminus(x : Value) -> Value raise {
  if x is Nil || numth__eqi(numth__gf_char(), 2) {
    return x
  }
  let mut r = cdr(x)
  while true {
    rplaca(r, gf_cminus_b(car(r))) |> ignore
    if cdr(r) is Nil {
      return x
    }
    r = cddr(r)
  }
  x
}

///|
/// x + y
fn gf_plus(x : Value, y : Value) -> Value raise {
  if x is Nil {
    y
  } else if y is Nil {
    x
  } else {
    gf_nplus(copy_list(x), y)
  }
}

///|
/// merge y into x (modifies x)
fn gf_nplus(x : Value, y : Value) -> Value raise {
  if x is Nil {
    return y
  }
  if y is Nil {
    return x
  }
  let mut x = x
  let mut y = y
  let mut cy : Value = Fix(0L)
  let mut ey : Value = Fix(0L)
  let mut r : Value = Nil
  // states of the prog: 0 = a1, 1 = a, 2 = b
  let mut state = 0
  while true {
    if state == 0 {
      // a1
      let ex = car(x)
      ey = car(y)
      cy = cadr(y)
      if num_gt(ey, ex) {
        x = cons(ey, cons(cy, x))
        y = cddr(y)
      } else if num_eq(ey, ex) {
        let c = gf_cplus_b(cadr(x), cy)
        y = cddr(y)
        if numth__eqi(c, 0) {
          x = cddr(x)
          if x is Nil {
            return y
          }
          if y is Nil {
            return x
          }
          continue
        } else {
          rplaca(cdr(x), c) |> ignore
        }
      } else {
        r = cdr(x)
        state = 2
        continue
      }
      r = cdr(x)
      state = 1
    } else if state == 1 {
      // a
      if y is Nil {
        return x
      }
      ey = car(y)
      cy = cadr(y)
      state = 2
    } else {
      // b
      while cdr(r).truthy() && num_gt(cadr(r), ey) {
        r = cddr(r)
      }
      if cdr(r) is Nil {
        rplacd(r, y) |> ignore
        return x
      } else if num_gt(ey, cadr(r)) {
        rplacd(r, cons(ey, cons(cy, cdr(r)))) |> ignore
        r = cddr(r)
        y = cddr(y)
      } else {
        let c = gf_cplus_b(caddr(r), cy)
        y = cddr(y)
        if numth__eqi(c, 0) {
          rplacd(r, cdddr(r)) |> ignore
        } else {
          r = cddr(r)
          rplaca(r, c) |> ignore
        }
      }
      state = 1
    }
  }
  x
}

///|
/// x + c*v^e*y
fn gf_xyecplus(x : Value, y : Value, e : Value, c : Value) -> Value raise {
  if y is Nil {
    x
  } else if x is Nil {
    gf_xectimes(y, e, c)
  } else {
    gf_nxyecplus(copy_list(x), y, e, c)
  }
}

///|
/// merge c*v^e*y into x (modifies x)
fn gf_nxyecplus(x : Value, y : Value, e : Value, c : Value) -> Value raise {
  if y is Nil {
    return x
  }
  if x is Nil {
    return gf_xectimes(y, e, c)
  }
  let mut x = x
  let mut y = y
  let mut cy : Value = Fix(0L)
  let mut ey : Value = Fix(0L)
  let mut r : Value = Nil
  // states of the prog: 0 = a1, 1 = a, 2 = b, 3 = d
  let mut state = 0
  while true {
    if state == 0 {
      // a1
      ey = num_add(car(y), e)
      cy = gf_ctimes(c, cadr(y))
      let ex = car(x)
      if num_gt(ey, ex) {
        x = cons(ey, cons(cy, x))
        y = cddr(y)
      } else if num_eq(ey, ex) {
        let cc = gf_cplus_b(cadr(x), cy)
        y = cddr(y)
        if numth__eqi(cc, 0) {
          x = cddr(x)
          if x is Nil {
            return gf_xectimes(y, e, c)
          }
          if y is Nil {
            return x
          }
          continue
        } else {
          rplaca(cdr(x), cc) |> ignore
        }
      } else {
        r = cdr(x)
        state = 2
        continue
      }
      r = cdr(x)
      state = 1
    } else if state == 1 {
      // a
      if y is Nil {
        return x
      }
      ey = num_add(car(y), e)
      cy = gf_ctimes(c, cadr(y))
      state = 2
    } else if state == 2 {
      // b
      if cdr(r) is Nil {
        state = 3
        continue
      }
      let ex = cadr(r)
      if num_gt(ey, ex) {
        rplacd(r, cons(ey, cons(cy, cdr(r)))) |> ignore
        r = cddr(r)
        y = cddr(y)
        state = 1
      } else if num_eq(ey, ex) {
        let cc = gf_cplus_b(caddr(r), cy)
        if numth__eqi(cc, 0) {
          rplacd(r, cdddr(r)) |> ignore
        } else {
          r = cddr(r)
          rplaca(r, cc) |> ignore
        }
        y = cddr(y)
        state = 1
      } else {
        r = cddr(r)
      }
    } else {
      // d
      while y is Cons(_) {
        x = nconc(x, list2(num_add(car(y), e), gf_ctimes(c, cadr(y))))
        y = cddr(y)
      }
      return x
    }
  }
  x
}

///|
/// x * y
///
/// For sparse polynomials (in Galois Fields) with not too high degrees
/// simple school multiplication is faster than Karatsuba.
///
/// x * y = (x1 + x2 + ... + xk) * (y1 + y2 + ... + yn)
///       =  x1 * (y1 + y2 + ... + yn) + x2 * (y1 + y2 + ... + yn) + ...
///
///         where e.g. xi = ci*v^ei
fn gf_times(x : Value, y : Value, red : Value) -> Value raise {
  if x is Nil || y is Nil {
    return Nil
  }
  // x1 * (y1 + y2 + ... + yn). summands in res are sorted. res is a new list.
  let res = gf_xectimes(y, car(x), cadr(x))
  // r1 marks the place of xi*y1 in res. x[i+1]*y1 will be smaller.
  let mut r1 = cdr(res)
  let mut x = cddr(x) // each loop: res += xi * (y1 + y2 + ... + yn)
  while !(x is Nil || y is Nil) {
    let mut ry = y // start with y1 again
    let ex = car(x) // xi = ci*v^ei
    let cx = cadr(x)
    let mut e = num_add(ex, car(ry)) // c*v^e = xi*y1
    let mut c = gf_ctimes(cadr(ry), cx) // zero divisor free mult in Fp^n
    while cdr(r1).truthy() && num_lt(e, cadr(r1)) {
      r1 = cddr(r1) // mark the position of xi*y1
    }
    let mut r = r1
    while true {
      // merge xi*y1 into res and then xi*y2, etc...
      if cdr(r) is Nil || num_gt(e, cadr(r)) {
        rplacd(r, cons(e, cons(c, cdr(r)))) |> ignore
        r = cddr(r)
      } else {
        c = gf_cplus_b(caddr(r), c)
        if numth__eqi(c, 0) {
          rplacd(r, cdddr(r)) |> ignore
        } else {
          r = cddr(r)
          rplaca(r, c) |> ignore
        }
      }
      ry = cddr(ry)
      if ry is Nil {
        break
      }
      e = num_add(ex, car(ry))
      c = gf_ctimes(cadr(ry), cx)
      while cdr(r).truthy() && num_lt(e, cadr(r)) {
        r = cddr(r)
      }
    }
    x = cddr(x)
  }
  gf_nred(res, red)
}

///|
/// x^2
///
/// x * x = (x_1 + x_2 + ... + x_k) * (x_1 + x_2 + ... + x_k)
///
///       = x_1^2 + 2*x_1*x_2 + 2*x_1*x_3 + ... + x_2^2 + 2*x_2*x_3 + ...
///
///       = x_k^2 + x_{k-1}^2 + 2*x_{k-1}*xk + x_{k-2}^2 + 2*x_{k-2}*x_{k-1}
///         + 2*x_{k-2}*xk + ...
///
/// The reverse needs some additional consing but is slightly faster.
fn gf_sq(x : Value, red : Value) -> Value raise {
  if x is Nil {
    return x
  }
  if !numth__efp() && eql(numth__gf_char(), Fix(2L)) {
    // the mod 2 case degrades to x_1^2 + x_2^2 + ... + x_k^2
    let mut x = x
    let mut res : Value = Nil
    while x is Cons(_) {
      res = cons(Fix(1L), cons(ash(car(x), 1), res))
      x = cddr(x)
    }
    return gf_nred(nreverse(res), red)
  }
  let mut x = reverse(x) // start with x_k
  let mut res : Value = Nil // result
  let mut r : Value = Nil // insertion marker in res
  let mut acc : Value = Nil // acc accumulates previous x_i
  let mut r1 : Value = Nil // r1 iterates in each loop over acc
  let mut ci : Value = Fix(0L)
  let mut ei : Value = Fix(0L)
  let mut two_ci : Value = Fix(0L)
  let mut at_a1 = true
  while true {
    if at_a1 {
      // a1
      ci = car(x) // x_i = ci*v^ei
      ei = cadr(x)
      two_ci = gf_cplus_b(ci, ci) // 2*ci (2*ci # 0 when *gf-char* # 2)
      res = cons(num_add(ei, ei), cons(gf_ctimes(ci, ci), res)) // res += x_i^2
      r = cdr(res) // place insertion marker behind x_i^2
      r1 = acc
      at_a1 = false
    }
    // a
    if r1 is Nil || numth__eqi(two_ci, 0) {
      // in ef *2ci might be 0 !
      x = cddr(x)
      if x is Nil {
        return gf_nred(res, red)
      }
      acc = cons(ei, cons(ci, acc)) // cons previous x_i to acc ..
      at_a1 = true // .. and start next loop
      continue
    }
    let e = num_add(ei, car(r1))
    let mut c = gf_ctimes(two_ci, cadr(r1))
    r1 = cddr(r1)
    while num_lt(e, cadr(r)) {
      r = cddr(r)
    }
    if num_gt(e, cadr(r)) {
      rplacd(r, cons(e, cons(c, cdr(r)))) |> ignore
      r = cddr(r)
    } else {
      c = gf_cplus_b(c, caddr(r))
      if numth__eqi(c, 0) {
        rplacd(r, cdddr(r)) |> ignore
      } else {
        r = cddr(r)
        rplaca(r, c) |> ignore
      }
    }
  }
  Nil
}

///|
/// x^n mod y; assume 0 <= n
fn gf_pow(x : Value, n : Value, red : Value) -> Value raise {
  if numth__eqi(n, 0) {
    return list2(Fix(0L), Fix(1L))
  }
  if x is Nil {
    return Nil
  }
  let mut x = x
  let mut n = n
  let mut res : Value = Nil
  while true {
    if oddp(n) {
      res = if res.truthy() { gf_times(x, res, red) } else { x }
      if numth__eqi(n, 1) {
        return res
      }
    }
    n = ash(n, -1)
    x = gf_sq(x, red)
  }
  Nil
}

///|
/// in a field use precomputed *gf-x^p-powers* resp. *ef-x^q-powers*
fn gf_pow_dol(x : Value, n : Value, red : Value) -> Value raise {
  if numth__efp() {
    if symval(q_ear_ef_irred_q).truthy() {
      n_starf_pow_dol(
        x,
        n,
        red,
        numth__gf_card(),
        symval(q_ear_ef_card),
        symval(q_ear_ef_x_hatq_powers),
      )
    } else {
      gf_pow(x, n, red)
    }
  } else if symval(q_ear_gf_irred_q).truthy() {
    n_starf_pow_dol(
      x,
      n,
      red,
      numth__gf_char(),
      numth__gf_card(),
      symval(q_ear_gf_x_hatp_powers),
    )
  } else {
    gf_pow(x, n, red)
  }
}

///|
fn n_starf_pow_dol(
  x : Value,
  n : Value,
  red : Value,
  p : Value,
  card : Value,
  x_hatp_powers : Value,
) -> Value raise {
  if numth__eqi(n, 0) {
    return list2(Fix(0L), Fix(1L))
  }
  if x is Nil {
    return Nil
  }
  if num_ge(n, card) {
    return gf_pow(x, n, red)
  }
  let mut prod = list2(Fix(0L), Fix(1L))
  let mut j = 0
  let mut n_base_p : Value = Nil
  let mut n = n
  while !numth__eqi(n, 0) {
    let (quo, r) = num_truncate(n, b=p)
    n_base_p = cons(r, n_base_p)
    n = quo
  }
  for ni in nreverse(n_base_p).iter() {
    let y = gf_compose(aref1(x_hatp_powers, j), x, red)
    let y = gf_pow(y, ni, red)
    prod = gf_times(prod, y, red)
    j += 1
  }
  prod
}

///|
/// remainder: x - quotient(x, y) * y
fn gf_rem(x : Value, y : Value) -> Value raise {
  if y is Nil {
    numth__quotient_by_zero() |> ignore
  }
  if x is Nil {
    x
  } else {
    gf_nrem(copy_list(x), y)
  }
}

///|
/// modifies x
fn gf_nrem(x : Value, y : Value) -> Value raise {
  if y is Nil {
    numth__quotient_by_zero() |> ignore
  }
  if x is Nil {
    return x
  }
  let lcy_inv = gf_cinv(cadr(y))
  let ley = car(y)
  let lcy_inv = gf_cminus_b(lcy_inv)
  let y = cddr(y)
  let mut x = x
  while x is Cons(_) {
    let e = num_sub(car(x), ley)
    if minusp(e) {
      return x
    }
    let lcx = cadr(x)
    let c = gf_ctimes(lcx, lcy_inv)
    x = gf_nxyecplus(cddr(x), y, e, c)
  }
  x
}

///|
/// reduce x by red (modifies x)
///
/// assume lc(red) = 1, reduction poly is monic
fn gf_nred(x : Value, red : Value) -> Value raise {
  if x is Nil || red is Nil {
    return x
  }
  let le_red = car(red)
  let red = cddr(red)
  let mut x = x
  while x is Cons(_) {
    let e = num_sub(car(x), le_red)
    if minusp(e) {
      return x
    }
    x = gf_nxyecplus(cddr(x), red, e, gf_cminus_b(cadr(x)))
  }
  x
}

///|
/// (monic) gcd
fn gf_gcd(x : Value, y : Value) -> Value raise {
  if x is Nil {
    return y
  }
  if y is Nil {
    return x
  }
  let mut x = x
  let mut y = y
  while y is Cons(_) {
    let r = gf_rem(x, y)
    x = y
    y = r
  }
  if eql(Fix(0L), car(x)) {
    list2(Fix(0L), Fix(1L))
  } else {
    gf_xctimes(x, gf_cinv(cadr(x)))
  }
}

///|
/// (monic) extended gcd
fn gf_gcdex(x : Value, y : Value, red : Value) -> Value raise {
  let mut x = x
  let mut y = y
  let mut x1 = list2(Fix(0L), Fix(1L))
  let mut x2 : Value = Nil
  let mut y1 : Value = Nil
  let mut y2 = list2(Fix(0L), Fix(1L))
  while y is Cons(_) {
    let (q, r) = gf_divide(x, y)
    x = y
    y = r
    let ny1 = gf_nplus(gf_nminus(gf_times(q, y1, red)), x1)
    x1 = y1
    y1 = ny1
    let ny2 = gf_nplus(gf_nminus(gf_times(q, y2, red)), x2)
    x2 = y2
    y2 = ny2
  }
  let inv = gf_cinv(cadr(x))
  mapcar(a => gf_xctimes(a, inv), list3(x1, x2, x))
}

///|
/// inversion: y^-1
///
/// in case the inverse does not exist it returns nil
/// (might happen when reduction poly isn't irreducible)
fn gf_inv(y : Value, red : Value) -> Value raise {
  if y is Nil {
    numth__quotient_by_zero() |> ignore
  }
  let mut y1 = list2(Fix(0L), Fix(1L))
  let mut x = red
  let mut x1 : Value = Nil
  let mut y = copy_list(y)
  while y is Cons(_) {
    let (q, r) = gf_divide(x, y)
    x = y
    y = r
    let ny1 = gf_nplus(gf_nminus(gf_times(q, y1, red)), x1)
    x1 = y1
    y1 = ny1
  }
  if numth__eqi(car(x), 0) {
    // gcd = 1 (const)
    gf_nxctimes(x1, gf_cinv(cadr(x)))
  } else {
    Nil
  }
}

///|
/// quotient and remainder
fn gf_divide(x : Value, y : Value) -> (Value, Value) raise {
  if y is Nil {
    numth__quotient_by_zero() |> ignore
    return (Nil, Nil)
  }
  if x is Nil {
    return (Nil, Nil)
  }
  let lcyi = gf_cinv(cadr(y))
  let ley = car(y)
  let mut x = copy_list(x)
  let mut q : Value = Nil
  let y = cddr(y)
  while x is Cons(_) {
    let e = num_sub(car(x), ley)
    if minusp(e) {
      return (nreverse(q), x)
    }
    let lcx = cadr(x)
    x = cddr(x)
    let c = gf_ctimes(lcx, lcyi)
    if y.truthy() {
      x = gf_nxyecplus(x, y, e, gf_cminus_b(c))
    }
    q = cons(c, cons(e, q))
  }
  (nreverse(q), x)
}

// polynomial/number/list - conversions ----------------------------------------

///|
/// poly 2 number:
fn d_ef_p2n(p : Value) -> Value raise {
  gf_data_q(Str("ef_p2n")) |> ignore
  numth__ef(t, fn() { gf_x2n(gf_p2x(p)) })
}

///|
fn d_gf_p2n(p : Value, gf_char? : Value = Nil) -> Value raise {
  numth__ef(Nil, fn() {
    if gf_char.truthy() {
      numth__with_char(gf_char, fn() { gf_x2n(gf_p2x(p)) })
    } else if symval(q_ear_gf_char_q).truthy() {
      gf_x2n(gf_p2x(p))
    } else {
      numth__err("`gf_p2n': missing modulus.", [])
    }
  })
}

///|
fn gf_x2n(x : Value) -> Value raise {
  if x is Nil {
    return Fix(0L)
  }
  let m = if numth__efp() { numth__gf_card() } else { numth__gf_char() }
  let mut x = x
  let mut n : Value = Fix(0L)
  while true {
    n = num_add(n, cadr(x))
    if cddr(x) is Nil {
      return num_mul(n, expt(m, car(x)))
    } else {
      n = num_mul(n, expt(m, num_sub(car(x), caddr(x))))
    }
    x = cddr(x)
  }
  Nil
}

///|
/// number 2 poly:
fn gf_n2p_errchk(fun : Value, n : Value) -> Value raise {
  if !integerp(n) {
    numth__err("`~m': Not an integer: ~m", [fun, n])
  } else {
    Nil
  }
}

///|
fn d_gf_n2p(n : Value, gf_char? : Value = Nil) -> Value raise {
  gf_n2p_errchk(Str("gf_n2p"), n) |> ignore
  numth__ef(Nil, fn() {
    if gf_char.truthy() {
      gf_set_rat_header() |> ignore
      numth__with_char(gf_char, fn() { gf_x2p(gf_n2x(n)) })
    } else if symval(q_ear_gf_char_q).truthy() {
      gf_x2p(gf_n2x(n))
    } else {
      numth__err("`gf_n2p': missing modulus.", [])
    }
  })
}

///|
fn d_ef_n2p(n : Value) -> Value raise {
  gf_data_q(Str("ef_n2p")) |> ignore
  gf_n2p_errchk(Str("ef_n2p"), n) |> ignore
  numth__ef(t, fn() { gf_x2p(gf_n2x(n)) })
}

///|
fn gf_n2x(n : Value) -> Value raise {
  let m = if numth__efp() { numth__gf_card() } else { numth__gf_char() }
  let mut e = 0
  let mut n = n
  let mut x : Value = Nil
  while !numth__eqi(n, 0) {
    let (q, r) = num_truncate(n, b=m)
    n = q
    if !numth__eqi(r, 0) {
      x = cons(numth__i(e), cons(r, x))
    }
    e += 1
  }
  x
}

///|
/// poly 2 list:
fn d_ef_p2l(p : Value, len? : Value = Fix(0L)) -> Value raise {
  numth__ef(t, fn() { cons(numth__mlist(), gf_x2l(gf_p2x_raw(p), len)) }) // more flexibility ...
}

///|
/// len = 0 : no padding
fn d_gf_p2l(p : Value, len? : Value = Fix(0L)) -> Value raise {
  numth__ef(Nil, fn() { cons(numth__mlist(), gf_x2l(gf_p2x_raw(p), len)) }) // ... by omitting mod reduction
}

///|
fn gf_x2l(x : Value, len : Value) -> Value raise {
  let mut x = x
  let mut e = if x.truthy() { to_int(car(x)) } else { 0 }
  let len = to_int(len)
  let mut k = if e > len - 1 { e } else { len - 1 }
  let mut l : Value = Nil
  while k >= 0 {
    if x is Nil || k > e {
      l = cons(Fix(0L), l)
    } else if k == e {
      l = cons(cadr(x), l)
      x = cddr(x)
      if x.truthy() {
        e = to_int(car(x))
      }
    }
    k -= 1
  }
  nreverse(l)
}

///|
/// list 2 poly:
fn d_ef_l2p(l : Value) -> Value raise {
  gf_l2p_errchk(l, Str("ef_l2p")) |> ignore
  numth__ef(t, fn() { gf_x2p(gf_l2x(cdr(l))) })
}

///|
fn d_gf_l2p(l : Value) -> Value raise {
  gf_l2p_errchk(l, Str("gf_l2p")) |> ignore
  numth__ef(Nil, fn() { gf_x2p(gf_l2x(cdr(l))) })
}

///|
fn gf_l2p_errchk(l : Value, fun : Value) -> Value raise {
  if !d_listp(l).truthy() {
    numth__err("`~m': Argument must be a list of integers.", [fun])
  } else {
    Nil
  }
}

///|
fn gf_l2x(l : Value) -> Value raise {
  let mut l = reverse(l)
  let mut e = 0
  let mut x : Value = Nil
  while l is Cons(_) {
    let c = car(l)
    if !numth__eqi(c, 0) {
      x = cons(numth__i(e), cons(c, x))
    }
    l = cdr(l)
    e += 1
  }
  x
}

///|
/// list 2 number:
fn d_gf_l2n(l : Value) -> Value raise {
  gf_char_q(Str("gf_l2n")) |> ignore
  gf_l2p_errchk(l, Str("gf_l2n")) |> ignore
  numth__ef(Nil, fn() { gf_l2n(cdr(l)) })
}

///|
fn d_ef_l2n(l : Value) -> Value raise {
  gf_data_q(Str("ef_l2n")) |> ignore
  gf_l2p_errchk(l, Str("ef_l2n")) |> ignore
  numth__ef(t, fn() { gf_l2n(cdr(l)) })
}

///|
fn gf_l2n(l : Value) -> Value raise {
  let m = if numth__efp() { numth__gf_card() } else { numth__gf_char() }
  let c1 = car(l)
  let mut l = reverse(cdr(l))
  let mut n : Value = Fix(0L)
  let mut b : Value = Fix(1L)
  while l is Cons(_) {
    let c = car(l)
    if !numth__eqi(c, 0) {
      n = num_add(n, num_mul(c, b))
    }
    b = num_mul(b, m)
    l = cdr(l)
  }
  num_add(num_mul(c1, b), n)
}

///|
/// number 2 list:
/// in case of len = 0 the list isn't padded or truncated
fn d_gf_n2l(n : Value, len? : Value = Fix(0L)) -> Value raise {
  gf_char_q(Str("gf_n2l")) |> ignore
  gf_n2p_errchk(Str("gf_n2l"), n) |> ignore
  cons(
    numth__mlist(),
    numth__ef(Nil, fn() {
      if numth__eqi(len, 0) {
        gf_n2l(n)
      } else {
        gf_n2l_twoargs(n, len)
      }
    }),
  )
}

///|
/// in case of len = 0 the list isn't padded or truncated
fn d_ef_n2l(n : Value, len? : Value = Fix(0L)) -> Value raise {
  gf_data_q(Str("ef_n2l")) |> ignore
  gf_n2p_errchk(Str("ef_n2l"), n) |> ignore
  cons(
    numth__mlist(),
    numth__ef(t, fn() {
      if numth__eqi(len, 0) {
        gf_n2l(n)
      } else {
        gf_n2l_twoargs(n, len)
      }
    }),
  )
}

///|
/// this version is frequently called by gf-precomp, keep it simple
fn gf_n2l(n : Value) -> Value raise {
  let m = if numth__efp() { numth__gf_card() } else { numth__gf_char() }
  let mut n = n
  let mut l : Value = Nil
  while !numth__eqi(n, 0) {
    let (q, r) = num_truncate(n, b=m)
    n = q
    l = cons(r, l)
  }
  l
}

///|
fn gf_n2l_twoargs(n : Value, len : Value) -> Value raise {
  let m = if numth__efp() { numth__gf_card() } else { numth__gf_char() }
  let mut n = n
  let mut len = to_int64(len)
  let mut l : Value = Nil
  while len != 0L {
    let (q, r) = num_truncate(n, b=m)
    n = q
    l = cons(r, l)
    len -= 1L
  }
  l
}
