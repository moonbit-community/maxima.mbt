// Port of src/float-properties.lisp: expose some properties of
// floating-point numbers (and bigfloats) to Maxima.

///|
/// CL FLOAT-PRECISION of a double: the number of significant bits (53 for
/// normalized numbers, fewer for denormals, 0 for zero).
fn float_properties__float_precision(d : Double) -> Int32 {
  if d == 0.0 {
    return 0
  }
  let raw = d.reinterpret_as_uint64()
  let e = ((raw >> 52) & 0x7ffUL).to_int()
  if e == 0 {
    // denormal: the significand is the raw fraction field
    let frac = raw & ((1UL << 52) - 1UL)
    64 - frac.clz()
  } else {
    53
  }
}

///|
/// The smallest exponent that decode-float can return for a normalized
/// number (+most-negative-normalized-float-exponent+).
fn float_properties__most_negative_normalized_float_exponent() -> Int32 {
  let expo = decode_float(least_positive_normalized_double_float).1
  // Some lisps may not have support for denormals.  In that case set the
  // exponent to be the exponent of the smallest float, add the number of
  // fraction bits, and subtract 1.
  if least_positive_double_float != least_positive_normalized_double_float {
    expo
  } else {
    expo + 53 - 1
  }
}

///|
let float_properties__float_bits_warned : Ref[Bool] = Ref::new(false)

///|
let float_properties__bigfloat_bits_warned : Ref[Bool] = Ref::new(false)

///|
/// The once-only warning printed by a DEFMFUN with :deprecated-p.
fn float_properties__deprecation_warning(
  done : Ref[Bool],
  name : Value,
  instead : Value,
) -> Unit raise {
  if !done.val {
    done.val = true
    mwarning(
      list1(
        aformat(Nil, Str("~M is deprecated; use ~M."), list([name, instead])),
      ),
    )
    |> ignore
  }
}

///|
/// Floating-point epsilon, basically the smallest value eps such that
/// 1+eps is not equal to 1.
fn d_float_eps() -> Value raise {
  Flo(double_float_epsilon)
}

///|
/// The bigfloat version of float_eps; the smallest bigfloat such that
/// 1+eps is not equal to 1.
fn d_bigfloat_eps() -> Value raise {
  let r = d_bfloat(div(Fix(1L), expt(Fix(2L), symval(q_fpprec))))
  list([first(r), one_plus(second(r)), third(r)])
}

///|
/// The number of bits in the fraction part of a floating-point number.
fn d_float_bits() -> Value raise {
  float_properties__deprecation_warning(
    float_properties__float_bits_warned, q_d_float_bits, q_d_float_precision,
  )
  Fix(53L)
}

///|
/// The number of bits in the fraction part of a bigfloat number.  Note
/// that this changes when $fpprec is changed, of course.
fn d_bigfloat_bits() -> Value raise {
  float_properties__deprecation_warning(
    float_properties__bigfloat_bits_warned, q_d_bigfloat_bits, q_d_float_precision,
  )
  symval(q_fpprec)
}

///|
/// The number of bits of precision in the floating-point number F.  This
/// includes floats and bigfloats.
fn d_float_precision(f : Value) -> Value raise {
  match f {
    Flo(d) => int(float_properties__float_precision(d))
    _ =>
      if d_bfloatp(f).truthy() {
        bigfloat_prec(f)
      } else {
        merr("~M: expected a float or bigfloat number: ~M", [
          q_d_float_precision, f,
        ])
      }
  }
}

// ULP is the Unit in the Last Place: the gap between x and the nearest
// other number.  For floating-point exact powers of two, the ulp is the gap
// to the next number down in magnitude, which is smaller than the gap to
// the next number up:
//    ulp(0.9999) = ulp(1.0) = ulp(1.0001)/2
// The ULP of all denormalized numbers is the same:
//    ulp(least_positive_float) = ulp(least_positive_float*2^53) = least_positive_float

///|
fn d_unit_in_last_place(f : Value) -> Value raise {
  if integerp(f) {
    Fix(1L)
  } else if ratnump(f).truthy() {
    Fix(0L)
  } else {
    match f {
      Flo(d) =>
        if d == 0.0 {
          symval(q_d_least_positive_float)
        } else {
          let (significand, expon, _) = decode_float(d)
          // If the exponent is smaller than the smallest normalized
          // exponent, the ULP is the smallest float.  Otherwise, the ULP
          // has an exponent that is float-digits smaller, except when the
          // fraction is a power of two, where we have to increase the
          // exponent by 1.
          if expon > float_properties__most_negative_normalized_float_exponent() {
            let adj = if d_is_power_of_two(Flo(significand)).truthy() {
              0
            } else {
              -1
            }
            Flo(scale_float(0.5, expon - 53 - adj))
          } else {
            symval(q_d_least_positive_float)
          }
        }
      _ =>
        if d_bfloatp(f).truthy() {
          let significand = cadr(f)
          let expon = num_sub(caddr(f), bigfloat_prec(f))
          if zerop(significand) {
            // ULP is arbitrarily small for bigfloat 0
            symval(q_ear_bigfloatzero)
          } else {
            // precision of resulting bigfloat not necessarily the same as
            // input but that doesn't matter, since 2^n can be represented
            // exactly in all precisions
            exptbigfloat(
              d_bfloat(Fix(2L)),
              if d_is_power_of_two(num_abs(significand)).truthy() {
                num_add(expon, Fix(-1L))
              } else {
                expon
              },
            )
          }
        } else {
          merr("~:@M: unit_in_last_place is not defined", [f])
        }
    }
  }
}

///|
/// is_power_of_two works for explicit numbers: integers, floats, bfloats,
/// rats.  NOTE: a negative number is not a power of 2.  Does NOT handle
/// expressions (by choice).
fn d_is_power_of_two(n : Value) -> Value raise {
  if integerp(n) {
    let a = num_abs(n)
    lbool(num_gt(n, Fix(0L)) && zerop(logand(a, num_add(a, Fix(-1L)))))
  } else {
    match n {
      Flo(d) => lbool(d > 0.0 && decode_float(d).0 == 0.5)
      _ =>
        if d_bfloatp(n).truthy() {
          d_is_power_of_two(cadr(n))
        } else if ratnump(n).truthy() {
          // ratnums not needed for unit_in_last_place, but let's be complete
          if num_eq(cadr(n), Fix(1L)) {
            d_is_power_of_two(caddr(n))
          } else {
            Nil
          }
        } else {
          merr("~:@M: is_power_of_two is only defined for numbers", [n])
        }
    }
  }
}

///|
/// Clamp a Lisp integer to an Int scale count.
fn float_properties__scale_count(n : Value) -> Int32 raise {
  if num_gt(n, Fix(100000L)) {
    100000
  } else if num_lt(n, Fix(-100000L)) {
    -100000
  } else {
    to_int(n)
  }
}

///|
/// A Maxima interface to CL:SCALE-FLOAT.  Basically computes f * 2^n,
/// but this should be exact.
fn d_scale_float(f : Value, n : Value) -> Value raise {
  if !integerp(n) {
    merr("scale_float: second arg must be an integer: ~M~%", [n]) |> ignore
  }
  match f {
    Flo(d) => Flo(scale_float(d, float_properties__scale_count(n)))
    _ =>
      if d_bfloatp(f).truthy() {
        // bigfloat:scale-float
        let r = bigfloatp(f)
        if zerop(cadr(r)) {
          bcons(list2(Fix(0L), Fix(0L)))
        } else {
          bcons(list2(cadr(r), num_add(caddr(r), n)))
        }
      } else {
        merr("scale_float: first arg must be a float or bfloat: ~M~%", [f])
      }
  }
}

///|
/// A Maxima interface to CL:DECODE-FLOAT which returns a list of a float,
/// exponent, and a sign such that (* sign (scale-float float exponent)) is
/// exactly the same number.  We return a mantissa in the range [1, 2)
/// instead of [0.5,1) because that's what IEEE mantissas are.  The
/// exponent is adjusted appropriately.
fn d_decode_float(f : Value) -> Value raise {
  match f {
    Flo(d) => {
      let (mant, expo, sign) = decode_float(d)
      list([list1(q_mlist), Flo(2.0 * mant), int(expo - 1), Flo(sign)])
    }
    _ =>
      if d_bfloatp(f).truthy() {
        // bigfloat:decode-float returns a mantissa |m|*2^-prec, the
        // exponent and the sign as a bigfloat.
        let r = bigfloatp(f)
        let m = cadr(r)
        let expo = caddr(r)
        list([
          list1(q_mlist),
          // (to (bigfloat:* mant 2))
          bcons(list2(num_abs(m), Fix(1L))),
          num_sub(expo, Fix(1L)),
          d_bfloat(signum(m)),
        ])
      } else {
        merr("decode_float is only defined for floats and bfloats: ~M", [f])
      }
  }
}

///|
/// A Maxima interface to CL:INTEGER-DECODE-FLOAT which returns a list of
/// an integer, an exponent and a sign such that (* sign (scale-float
/// (float integer 1d0) exponent)) returns the original number.  The
/// number of bits in the integer part is the same as (float-precision f).
fn d_integer_decode_float(f : Value) -> Value raise {
  match f {
    Flo(d) => {
      let (i, expo, sign) = integer_decode_float(d)
      let int_ = from_big(i)
      let shift = integer_length(int_) - float_properties__float_precision(d)
      // If shift > 0, we have a denormal and want to reduce the number of
      // bits in the integer part.
      if shift > 0 {
        list([list1(q_mlist), ash(int_, -shift), int(expo + shift), int(sign)])
      } else {
        list([list1(q_mlist), int_, int(expo), int(sign)])
      }
    }
    _ =>
      if d_bfloatp(f).truthy() {
        // bigfloat:integer-decode-float
        let r = bigfloatp(f)
        list([
          list1(q_mlist),
          num_abs(cadr(r)),
          num_sub(caddr(r), caddr(car(r))),
          signum(cadr(r)),
        ])
      } else {
        merr("decode_float is only defined for floats and bfloats: ~M", [f])
      }
  }
}

///|
/// The sign of the float F, which can either be a float or bigfloat.  The
/// sign is +1 or -1 depending on the sign of F.  It has the same type as F.
fn d_float_sign(f : Value) -> Value raise {
  match f {
    Flo(d) => Flo(if dsignbit(d) { -1.0 } else { 1.0 })
    _ =>
      if d_bfloatp(f).truthy() {
        let r = bigfloatp(f)
        if minusp(cadr(r)) {
          d_bfloat(Fix(-1L))
        } else {
          d_bfloat(Fix(1L))
        }
      } else {
        merr("float_sign is only defined for floats and bfloats: ~M", [f])
      }
  }
}

///|
fn d_float_infinity_p(x : Value) -> Value raise {
  match x {
    Flo(d) =>
      lbool(d > most_positive_double_float || d < -most_positive_double_float)
    _ => Nil
  }
}

///|
fn d_float_nan_p(x : Value) -> Value raise {
  match x {
    Flo(d) => lbool(d != d)
    _ => Nil
  }
}

///|
fn float_nan_p(x : Value) -> Value raise {
  match x {
    Flo(d) => lbool(!(d == d))
    _ => Nil
  }
}

///|
fn float_inf_p(x : Value) -> Value raise {
  if floatp(x) && !float_nan_p(x).truthy() {
    beyond_extreme_values(x)
  } else {
    Nil
  }
}

///|
fn beyond_extreme_values(x : Value) -> Value raise {
  let (most_negative, most_positive) = extreme_float_values(x)
  if num_lt(x, Fix(0L)) {
    lbool(num_lt(x, most_negative))
  } else if num_gt(x, Fix(0L)) {
    lbool(num_gt(x, most_positive))
  } else {
    Nil
  }
}

///|
/// The extreme values of the float type of X (the port has only doubles).
fn extreme_float_values(x : Value) -> (Value, Value) raise {
  match x {
    Flo(_) =>
      (Flo(-most_positive_double_float), Flo(most_positive_double_float))
    _ => (Nil, Nil)
  }
}

///|
fn init_float_properties() -> Unit raise {
  let neverset = list([kw("properties"), list1(list2(q_assign, q_neverset))])
  defvar_init(q_d_most_positive_float, Flo(most_positive_double_float))
  defmvar(
    q_d_most_positive_float,
    val=symval(q_d_most_positive_float),
    neverset,
  )
  |> ignore
  defvar_init(q_d_most_negative_float, Flo(-most_positive_double_float))
  defmvar(
    q_d_most_negative_float,
    val=symval(q_d_most_negative_float),
    neverset,
  )
  |> ignore
  // largest_float and largest_negative_float are deprecated constants.
  defvar_init(q_d_largest_float, symval(q_d_most_positive_float))
  defmvar(
    q_d_largest_float,
    val=symval(q_d_most_positive_float),
    list([kw("deprecated-p"), Str("Use most_positive_float.")]),
  )
  |> ignore
  defvar_init(q_d_largest_negative_float, symval(q_d_most_negative_float))
  defmvar(
    q_d_largest_negative_float,
    val=symval(q_d_most_negative_float),
    list([kw("deprecated-p"), Str("Use most_negative_float.")]),
  )
  |> ignore
  defvar_init(q_d_least_positive_float, Flo(least_positive_double_float))
  defmvar(
    q_d_least_positive_float,
    val=symval(q_d_least_positive_float),
    neverset,
  )
  |> ignore
  defvar_init(
    q_d_least_positive_normalized_float,
    Flo(least_positive_normalized_double_float),
  )
  defmvar(
    q_d_least_positive_normalized_float,
    val=symval(q_d_least_positive_normalized_float),
    neverset,
  )
  |> ignore
  defvar_init(q_d_least_negative_float, Flo(-least_positive_double_float))
  defmvar(
    q_d_least_negative_float,
    val=symval(q_d_least_negative_float),
    neverset,
  )
  |> ignore
  defvar_init(
    q_d_least_negative_normalized_float,
    Flo(-least_positive_normalized_double_float),
  )
  defmvar(
    q_d_least_negative_normalized_float,
    val=symval(q_d_least_negative_normalized_float),
    neverset,
  )
  |> ignore
}
