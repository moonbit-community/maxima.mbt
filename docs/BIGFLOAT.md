# Translating `bigfloat`-package code

Code after `(in-package :bigfloat)` (parts of specfn, gamma, ellipt,
hypergeometric, nfloat, intpol) and calls written `bigfloat:foo` from the
maxima package (combin, rpart, csimp2, float-properties, sinc, simp) use the
generic arithmetic of `numeric.lisp`. In that package the CL names `+ - * /
1+ 1- zerop plusp minusp abs sqrt log exp sin ... expt = /= < > <= >=
realpart imagpart complex conjugate max min cis phase floor ... float
random signum float-sign float-digits rational rationalize coerce incf
decf realp complexp numberp integer-decode-float decode-float scale-float`
are **shadowed** by the generic versions below. Other CL functions (`oddp`,
`evenp`, `integerp`, `floatp`, `rationalp`, `typep`, `ash`, `car`, ...) keep
their CL meaning.

The port is in `core/numeric_1.mbt` and `core/numeric_2.mbt`.

## Representation

| Lisp object | Port value |
|---|---|
| CL integer / ratio / double / complex | `Fix`/`Big`, `Ratio`, `Flo`, `Cplx(re, im)` |
| `BIGFLOAT` instance | `make_struct("bigfloat", [maxima-bigfloat])` |
| `COMPLEX-BIGFLOAT` instance | `make_struct("complex-bigfloat", [re, im])` (each a Maxima bigfloat) |

The slots hold full Maxima bigfloats `((bigfloat simp prec) mant exp)`.
There are no single floats: `1f0`, `1e0`, `single-float` are doubles.
A Maxima rational `((rat simp) 1 2)` is *not* a CL number; `bf_to`
converts it to `Ratio`.

## Conventions

- All functions are `raise`. A generic function with no applicable method
  raises a `SimpleError` (as CLOS's no-applicable-method).
- **Predicates and comparisons return MoonBit `Bool`** (`bf_zerop`,
  `bf_lt`, `bf_eq`, ...), so `(if (< a b) ...)` is `if bf_lt(a, b) {...}`.
  The n-ary Lisp forms (`bf_op_eq`, `bf_op_lt`, ...) return `t`/`Nil`.
- Functions returning CL multiple values return tuples
  (`bf_floor(x).0` for the primary value).
- `&rest` functions take a Lisp list (`bf_op_plus(list([a, b, c]))`);
  `bf_addn([..])` / `bf_muln([..])` take an array. For two arguments call
  the two-argument function directly (`(+ a b)` → `bf_add(a, b)`;
  `(+ a b c)` → `bf_add(bf_add(a, b), c)` — left-associative, same as
  the Lisp).
- `#'+` / `#'*` as a function value, e.g. `(reduce #'* l)` →
  `reduce((x, y) => bf_mul(x, y), l)`; the symbols `bigfloat::+` etc.
  also have function cells, so `funcall(q_bf_op_plus, ...)` works.
- `(incf x d)` → `x = bf_add(x, d)`; `(incf x)` → `x = bf_add(x, Fix(1L))`;
  `decf` likewise with `bf_sub`.

## Table

| Lisp (bigfloat package) | MoonBit | Notes |
|---|---|---|
| `(+ a b)` / `two-arg-+` | `bf_add(a, b)` | |
| `(+ &rest args)` | `bf_op_plus(args_list)` / `bf_addn([..])` | `(+)` = 0 |
| `(- a)` / `unary-minus` | `bf_neg(a)` | |
| `(- a b)` / `two-arg--` | `bf_sub(a, b)` | |
| `(- a &rest more)` | `bf_op_(a, more_list)` | |
| `(* a b)` / `two-arg-*` | `bf_mul(a, b)` | |
| `(* &rest args)` | `bf_op_star(args_list)` / `bf_muln([..])` | `(*)` = 1 |
| `(/ a)` / `unary-divide` | `bf_inv(a)` | |
| `(/ a b)` / `two-arg-/` | `bf_div(a, b)` | complex doubles use `bf_cdiv_double_float` when `*use-accurate-complex-div*` |
| `(/ a &rest more)` | `bf_op_sl(a, more_list)` | |
| `1+` / `add1` | `bf_1_plus(x)` (= `bf_add1`) | |
| `1-` / `sub1` | `bf_1_(x)` (= `bf_sub1`) | |
| `(= a b)` / `two-arg-=` | `bf_eq(a, b) -> Bool` | NB `(= x y)` calls `two-arg-=(y, x)`; result is the same |
| `(= a &rest more)` | `bf_op_eq(a, more_list) -> t/Nil` | |
| `(/= a b)` | `!bf_eq(a, b)` | n-ary: `bf_op_sl_eq(a, more_list)` |
| `(< a b)` `(> a b)` `(<= a b)` `(>= a b)` | `bf_lt`, `bf_gt`, `bf_le`, `bf_ge` `-> Bool` | reals and BIGFLOATs only |
| `(< a b c ...)` etc. | `bf_op_lt`, `bf_op_gt`, `bf_op_lt_eq`, `bf_op_gt_eq` `(a, more_list) -> t/Nil` | |
| `zerop` `plusp` `minusp` | `bf_zerop`, `bf_plusp`, `bf_minusp` `-> Bool` | plusp/minusp: reals and BIGFLOATs only |
| `realp` `complexp` `numberp` | `bf_realp`, `bf_complexp`, `bf_numberp` `-> Bool` | include the bigfloat classes |
| `(typep x 'bigfloat)` | `bf_is_bigfloat(x) -> Bool` | |
| `(typep x 'complex-bigfloat)` | `bf_is_complex_bigfloat(x) -> Bool` | |
| `(typep x 'numeric)` | `bf_is_numeric(x) -> Bool` | |
| `(make-instance 'bigfloat :real r)` | `bf_make_bigfloat(r)` | `r` a Maxima bigfloat |
| `(make-instance 'complex-bigfloat :real r :imag i)` | `bf_make_complex_bigfloat(r, i)` | |
| `real-value` / `imag-value` | `bf_real_value(x)`, `bf_imag_value(x)` | Maxima bigfloat rounded to fpprec |
| `abs` | `bf_abs(x)` | |
| `sqrt` | `bf_sqrt(x)` | no contagion: a CL rational gives a double |
| `exp` `sin` `cos` `tan` `asin` `acos` | `bf_exp`, `bf_sin`, `bf_cos`, `bf_tan`, `bf_asin`, `bf_acos` | |
| `sinh` `cosh` `tanh` `asinh` `acosh` `atanh` | `bf_sinh`, `bf_cosh`, `bf_tanh`, `bf_asinh`, `bf_acosh`, `bf_atanh` | |
| `(log a)` / `(log a b)` | `bf_log(a)` / `bf_log(a, b=b)` | also `bf_log1(a)`, `bf_log2(a, b)` |
| `(atan y)` / `(atan y x)` | `bf_atan(y)` / `bf_atan(y, b=x)` | also `bf_atan1`, `bf_atan2(y, x)` |
| `(expt a b)` | `bf_expt(a, b)` | |
| `(scale-float a n)` | `bf_scale_float(a, n)` | `n` an integer Value |
| `realpart` `imagpart` `conjugate` `phase` | `bf_realpart`, `bf_imagpart`, `bf_conjugate`, `bf_phase` | |
| `cis` | `bf_cis(x)` | |
| `(complex a)` / `(complex a b)` | `bf_complex(a)` / `bf_complex(a, b=b)` | also `bf_complex1`, `bf_complex2` |
| `(floor a)` / `(floor a d)` | `bf_floor(a)` / `bf_floor(a, divisor=d)` `-> (Value, Value)` | |
| `ffloor` `ceiling` `fceiling` `truncate` `ftruncate` `round` `fround` | `bf_ffloor`, `bf_ceiling`, `bf_fceiling`, `bf_truncate`, `bf_ftruncate`, `bf_round`, `bf_fround` (same shape) | |
| `unary-floor` etc. (BIGFLOAT only) | `bf_unary_floor`, `bf_unary_ffloor`, `bf_unary_truncate`, `bf_unary_ftruncate`, `bf_unary_ceiling`, `bf_unary_fceiling` | |
| `(max a &rest more)` / `min` | `bf_max(a, more_list)`, `bf_min(a, more_list)` | `(max a b)` → `bf_max(a, list1(b))` |
| `(float x y)` | `bf_float(x, y)` | `y` a float or BIGFLOAT prototype |
| `epsilon` | `bf_epsilon(x)` | |
| `integer-decode-float` | `bf_integer_decode_float(x) -> (m, e, s)` | |
| `decode-float` | `bf_decode_float(x) -> (f, e, s)` | |
| `float-sign` (1 arg) | `bf_float_sign(x)` | |
| `float-digits` | `bf_float_digits(x)` | |
| `signum` | `bf_signum(x)` | |
| `rational` / `rationalize` | `bf_rational(x)`, `bf_rationalize(x)` | |
| `(random x)` / `(random x state)` | `bf_random(x)` / `bf_random(x, state=s)` | uses `mt_random` |
| `(coerce x type)` | `bf_coerce(x, type)` | type a symbol (`sym("double-float")`, `q_bigfloat`, ...) or `(complex flonum)` list |
| `%pi` / `%e` | `bf_p_pi(x)`, `bf_p_e(x)` | value with the precision of `x` |
| `(bigfloat re)` / `(bigfloat re im)` | `bf_bigfloat(re)` / `bf_bigfloat(re, im=im)` | |
| `intofp` (bigfloat package) | `bf_intofp(x)` | ≠ Maxima's `intofp` |
| `to` / `bigfloat:to` | `bf_to(x)` / `bf_to(re, imag=im)` | Maxima number → CL number / bigfloat object; merrors if impossible |
| `maybe-to` | `bf_maybe_to(x)` | |
| `%to` | `bf_p_to(x)` | no error handling |
| `maxima::to` (also plain `to` in maxima-package code) | `maxima_to(x)` | bigfloat object / CL number → Maxima number; others unchanged. Function cell of symbol `to` (`q_to`). |
| `max-exponent` | `bf_max_exponent(x)` | |
| `expt-extra-bits` | `bf_expt_extra_bits(x, a)` | |
| `(with-extra-precision (extra (a b)) body)` | `bf_with_extra_precision(extra, [a, b], vs => body)` | `vs[0]`, `vs[1]` are the rebound `a`, `b` |
| `lentz` | `bf_lentz(bf, af)` (primary value); `bf_lentz_mv(bf, af) -> (f, j, tiny)` | `bf`/`af` are Lisp function values: `lfunc("..", args => ...)` |
| `sum-power-series` | `bf_sum_power_series(x, f)` | `f` a Lisp function value |
| `format-e` `format-f` `format-g` | `bf_format_e`, `bf_format_f`, `bf_format_g` | |
| `cdiv-double-float` | `bf_cdiv_double_float(x, y)` | |
| `fp2single` | `bf_fp2single(l)` | double result rounded to 24 bits |
| `incf` / `decf` | see Conventions | |

Function cells: every generic function above is installed on its Lisp
symbol (`bigfloat::abs`, `bigfloat::two-arg-+`, `bigfloat::<`, ...; the
`defun`s are installed by the registry), plus `to` for `maxima::to`.
Predicates return `t`/`Nil` and multiple-value functions return their
primary value when called through `funcall`.

Special variables (no `q_` constants; use `sym(...)`):
`bigfloat::*use-accurate-complex-div*` (t), `bigfloat::*debug-cf-eval*`
(nil), `bigfloat::*max-cf-iterations*` (10000).

## Other functions declared for bigfloat-package code in other files

ellipt's `bf_agm` is declared returning 4 values (a tuple). Functions
defined with `defun` in other files' bigfloat sections are declared in
`core/gen_decls.mbt` with the `bf_` prefix (`bf_sn`, `bf_bf_rf`,
`bf_bf_erf`, `bf_lambert_w_k`, ...) — implement those in your file.

## Examples

```lisp
(defun descending-base-p (u m)
  (and (< (abs m) (epsilon u))
       (or (realp u)
           (zerop m)
           (< (abs m) (* (epsilon u) (exp (* -2 (abs (imagpart u)))))))))
```

```moonbit
fn bf_descending_base_p(u : Value, m : Value) -> Value raise {
  lbool(
    bf_lt(bf_abs(m), bf_epsilon(u)) &&
    (bf_realp(u) ||
    bf_zerop(m) ||
    bf_lt(
      bf_abs(m),
      bf_mul(bf_epsilon(u), bf_exp(bf_mul(Fix(-2L), bf_abs(bf_imagpart(u))))),
    )),
  )
}
```

`(multiple-value-bind (q r) (floor x 2) ...)` →
`let (q, r) = bf_floor(x, divisor=Fix(2L))`.
