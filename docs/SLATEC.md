# SLATEC and QUADPACK in MoonBit (`dii/maxima/slatec`)

Maxima ships the numerical Fortran libraries it needs as f2cl-generated Lisp
(`.repos/maxima/src/numerical/slatec/*.lisp`, run on the f2cl runtime
`numerical/f2cl-lib.lisp`): SLATEC special functions (Bessel, Airy, gamma,
error function, exponential integral, Spence's function and their helpers)
and QUADPACK (`dq*`). The package `slatec/` is a MoonBit translation of all
of them, with native types, that reproduces the Lisp results bit for bit.
`numerical/slatec/quadpack.lisp` (the Maxima-side `$quad_qags` etc.) is *not*
part of it; that glue belongs to the core port and calls into this package.

To use it from a package, add `"dii/maxima/slatec"` to its `moon.pkg` import
list and call `@slatec.<routine>`.

## Layout

| File | What |
|------|------|
| `slatec/<routine>.mbt` | **Generated** by `tools/f2cl2mbt.py`, one per Lisp file (118 routines). Never edit; regenerate. |
| `slatec/xerror.mbt` | Hand port of `xermsg`, `xerprn`, `xersve` (Fortran CHARACTER handling and formatted output). |
| `slatec/f2cl_runtime.mbt` | `d1mach`, `i1mach` and the f2cl-lib intrinsics (`sign`, `mod`, `max`/`min`, `int`, `aint`, ...). |
| `slatec/libm_native.mbt` | Native backend: `exp`, `log`, `pow`, `sin`, `cos`, `tan`, `atan`, `atan2`, `sinh`, `cosh`, `tanh` bound to the C libm (what SBCL calls). |
| `slatec/libm_portable.mbt` | Other backends: the same functions via `@math` (not guaranteed bit-exact). |
| `slatec/*_wbtest.mbt` | Tests (see Validation). |

Regenerate with

```sh
python3 tools/f2cl2mbt.py            # reads .repos/maxima/src/numerical/slatec, writes slatec/
```

The script parses every `defun` with its own small Lisp reader and
translates the f2cl constructs (`fref`, `fdo`, `with-multi-array-data`,
`array-slice`, `arithmetic-if`, `computed-goto`, `prog`/`tagbody`/`go`,
`multiple-value-bind`, the intrinsics) directly; no file needed hand fixes.

## Calling conventions

* **Types.** `double-float` → `Double`, `single-float` → `Float` (only used
  internally, e.g. the `eta` argument of `initds`), `integer4` → `Int`,
  `logical` → `Bool`, `(simple-)array double-float` → `FixedArray[Double]`,
  `(array integer4)` → `FixedArray[Int]`, Fortran strings → `String`.
  Complex numbers are, as in the AMOS Fortran, separate real/imaginary
  `Double`s (`zr, zi`; `cyr, cyi` arrays).
* **Arguments are passed exactly as in the Lisp call**, in the same order,
  including the dummy "output" scalars (Maxima passes `0.0`/`0` for them;
  most routines overwrite them before reading).
* **Arrays** are mutated in place and keep Fortran's 1-based indexing in the
  translated bodies: Fortran `Y(K)` is `y[k - 1]`. An array parameter that
  some internal caller passes as a *section* (f2cl `array-slice`) is
  followed by an extra `<name>_off : Int` parameter (the 0-based start of
  the section). None of the routines Maxima calls has such a parameter; they
  appear only on internal routines such as `dqagse`'s `alist_off`.
* **Results.** A Lisp f2cl function returns `(values ...)` with one slot
  per Fortran argument (preceded by the function value for a FUNCTION
  subprogram); slots for arguments the routine never returns are `NIL`.
  The MoonBit function returns **only the non-NIL slots, in order**: a bare
  value when there is one, a tuple when there are several, `Unit` when there
  are none. So translating a Maxima `multiple-value-bind` means: drop the
  variables bound to NIL slots (they are always among the `(declare (ignore
  ...))` ones) and destructure the rest positionally. The per-routine table
  below lists which arguments come back.
* **Integrands.** QUADPACK routines take `f : (Double) -> Double raise`.
  Every QUADPACK routine is `raise` and propagates whatever the integrand
  raises (Maxima's integrand `merror`s on non-float values and its
  `handler-case` turns any error into the unevaluated noun form; the core
  port should do the same with `try`/`catch` around the call).
* **Names.** Lisp names are kept (`dbesj0`), except that `$` becomes `_`
  (`zsqrt$` → `zsqrt_`, `last$` → `last_`) and parameter names that clash
  with a routine or keyword get `_v`/`_` (`djairy`'s `dai` → `dai_v`,
  `in` → `in_`).
* **State.** Fortran SAVE/DATA variables (first-call initialisations such as
  `ntj0`/`xsml` in `dbesj0`, the `j4save` parameters, the `xersve` message
  table) are package-level, like the Lisp `let` around each `defun`.

## Error handling

`xermsg` behaves exactly like the Lisp: it consults `j4save(2)` (control,
default 2: print full messages, "traceback requested") and `j4save(4)`
(maximum times a message is printed, default 10), records the message in the
`xersve` table, prints the report to standard output (the same lines Maxima
prints, including the summary table and f2cl's quirks such as `index`
returning a 0-based position), and then *returns*: `xerhlt` is f2cl's `STOP`,
which only returns because `*stop-signals-error-p*` is NIL. Callers'
error flags (`nz`, `ierr`, `ier`) are therefore identical to the Lisp.
`quad_control(current_error|control|max_message[, v])` maps to
`@slatec.j4save(1|2|4, v, true)` (set; returns the old value) or
`@slatec.j4save(k, 0, false)` (query).

## Routines called by Maxima

Signatures are as generated (`slatec/<name>.mbt`). "Maxima's Lisp" quotes
the call in `src/*.lisp` / `quadpack.lisp`; "returns" lists the non-NIL
slots.

### Real-argument special functions (FUNCTION subprograms)

All of these are `pub fn <name>(x : Double) -> Double` and are called in
Maxima as `(slatec:<name> x)`, using the first (only meaningful) value:

| Routine | Maxima use |
|---------|------------|
| `dbesj0`, `dbesj1` | `bessel_j(0|1, x)` (bessel.lisp) |
| `dbesy0`, `dbesy1` | `bessel_y(0|1, x)`, x > 0; for x < 0 combined with `dbesj0/1(-x)` |
| `dbesi0`, `dbesi1` | `bessel_i(0|1, x)` |
| `dbesk0`, `dbesk1` | `bessel_k(0|1, x)` |
| `dbsi0e`, `dbsi1e` | `scaled_bessel_i0(x)`, `scaled_bessel_i1(x)` |
| `dai`, `daie` | `airy_ai(x)` (airy.lisp: `dai` for x < 92.5747, else `daie(x)*exp(-2*x*sqrt(x)/3)` in newer sources) |
| `dbi` | `airy_bi(x)` for x < 104.2179765192136 |
| `derf` | `erf(x)` for floats (gamma.lisp `erf`) |
| `de1` | `expint(x)` (expintegral.lisp) |
| `dspenc` | `li[2](x)` for 0 <= x < 1 (specfn.lisp) |
| `dgamma` | `gammafloat` for 0 < a < 10 (csimp2.lisp) |
| `d9lgmc` | `gammafloat` for a >= 10: `sqrt(2*pi)*exp(d9lgmc(a))*...` |

### Real-argument Bessel sequences

```
pub fn dbesj(x : Double, alpha : Double, n : Int, y : FixedArray[Double], nz : Int) -> Int
pub fn dbesy(x : Double, fnu : Double, n : Int, y : FixedArray[Double]) -> Unit
pub fn dbesi(x : Double, alpha : Double, kode : Int, n : Int, y : FixedArray[Double], nz : Int) -> Int
pub fn dbesk(x : Double, fnu : Double, kode : Int, n : Int, y : FixedArray[Double], nz : Int) -> Int
```

Returns: `nz` (none for `dbesy`); `y[0..n-1]` hold orders
`alpha, alpha+1, ...`. Maxima splits the order with `(floor order)` into
`n` and `alpha`, allocates `(1+ n)` elements and reads `(aref jvals n)`:

```lisp
(slatec:dbesj (abs (float arg)) alpha (1+ n) jvals 0)      ; bessel_j
(slatec:dbesy (abs (float arg)) alpha (1+ n) jvals)        ; bessel_y
(slatec:dbesi (float (realpart arg)) alpha 1 (1+ n) jvals 0) ; bessel_i
(slatec:dbesi ($float $x) alpha 2 (1+ n) iarray 0)         ; scaled_bessel_i
(slatec:dbesk (float arg) alpha 1 (1+ n) jvals 0)          ; bessel_k
```

```moonbit
let jvals : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
let _nz = @slatec.dbesj(x.abs(), alpha, n + 1, jvals, 0)
jvals[n]
```

(`alpha` must be computed as SBCL's FLOOR does: `order - n.to_double()`.)

### Airy functions and derivatives, real argument

```
pub fn djairy(x : Double, rx : Double, c : Double, ai : Double, dai_v : Double) -> (Double, Double)
pub fn dyairy(x : Double, rx : Double, c : Double, bi : Double, dbi_v : Double) -> (Double, Double, Double, Double)
```

Returns: `djairy` → `(ai, dai)`; `dyairy` → `(rx, c, bi, dbi)`. Maxima
(airy.lisp) computes `rz = sqrt(|z|)`, `c = 2/3 * |z|^(3/2)` (in MoonBit
`2.0 / 3.0 * pow(|z|, 1.5)` with libm `pow`) and binds
`(var-0 var-1 var-2 ai dai)` / `(var-0 var-1 var-2 bi dbi)`:

```moonbit
let (_ai, dai) = @slatec.djairy(z, rz, c, 0.0, 0.0)          // airy_dai
let (_rx, _c, _bi, dbi) = @slatec.dyairy(z, rz, c, 0.0, 0.0) // airy_dbi (z < 104.1525)
```

### Complex argument (AMOS)

```
pub fn zbesj(zr : Double, zi : Double, fnu : Double, kode : Int, n : Int, cyr : FixedArray[Double], cyi : FixedArray[Double], nz : Int, ierr : Int) -> (Int, Int)
pub fn zbesi(zr : Double, zi : Double, fnu : Double, kode : Int, n : Int, cyr : FixedArray[Double], cyi : FixedArray[Double], nz : Int, ierr : Int) -> (Int, Int)
pub fn zbesk(zr : Double, zi : Double, fnu : Double, kode : Int, n : Int, cyr : FixedArray[Double], cyi : FixedArray[Double], nz : Int, ierr : Int) -> (Int, Int)
pub fn zbesy(zr : Double, zi : Double, fnu : Double, kode : Int, n : Int, cyr : FixedArray[Double], cyi : FixedArray[Double], nz : Int, cwrkr : FixedArray[Double], cwrki : FixedArray[Double], ierr : Int) -> (Int, Int)
pub fn zbesh(zr : Double, zi : Double, fnu : Double, kode : Int, m : Int, n : Int, cyr : FixedArray[Double], cyi : FixedArray[Double], nz : Int, ierr : Int) -> (Int, Int)
pub fn zairy(zr : Double, zi : Double, id : Int, kode : Int, air : Double, aii : Double, nz : Int, ierr : Int) -> (Double, Double, Int, Int)
pub fn zbiry(zr : Double, zi : Double, id : Int, kode : Int, bir : Double, bii : Double, ierr : Int) -> (Double, Double, Int)
```

Returns: `zbes*` → `(nz, ierr)`; `zairy` → `(air, aii, nz, ierr)`;
`zbiry` → `(bir, bii, ierr)`. Results of the `zbes*` routines are in
`cyr`/`cyi`. Maxima's calls and their MoonBit form:

| Maxima's Lisp | MoonBit |
|---------------|---------|
| `(multiple-value-bind (v-zr v-zi v-fnu v-kode v-n v-cyr v-cyi v-nz v-ierr) (slatec:zbesj zr zi alpha 1 (1+ n) cyr cyi 0 0) ...)` | `let (nz, ierr) = @slatec.zbesj(zr, zi, alpha, 1, n + 1, cyr, cyi, 0, 0)`; result `(cyr[n], cyi[n])` |
| `(slatec::zbesy zr zi alpha 1 (1+ n) cyr cyi 0 cwrkr cwrki 0)` binding `(... v-nz v-cwrkr v-cwrki v-ierr)` | `let (nz, ierr) = @slatec.zbesy(zr, zi, alpha, 1, n + 1, cyr, cyi, 0, cwrkr, cwrki, 0)` |
| `(slatec::zbesi zr zi alpha 1 (1+ n) cyr cyi 0 0)` | `@slatec.zbesi(...)` likewise |
| `(slatec::zbesk zr zi alpha 1 (1+ n) cyr cyi 0 0)` | `@slatec.zbesk(...)` likewise |
| `(slatec::zbesh zr zi fnu 1 1 (1+ n) cyr cyi 0 0)` (hankel_1; `m = 2` for hankel_2), binding `(dzr dzi df dk dm dn dcyr dcyi nz ierr)` | `let (nz, ierr) = @slatec.zbesh(zr, zi, fnu, 1, 1, n + 1, cyr, cyi, 0, 0)` |
| `(multiple-value-bind (var-0 var-1 var-2 var-3 air aii nz ierr) (slatec:zairy zr zi 0 1 0.0 0.0 0 0))` (airy_ai; `id = 1` for airy_dai) | `let (air, aii, nz, ierr) = @slatec.zairy(zr, zi, 0, 1, 0.0, 0.0, 0, 0)` |
| `(multiple-value-bind (var-0 var-1 var-2 var-3 bir bii ierr) (slatec:zbiry zr zi 0 1 0.0 0.0 0))` (airy_bi; `id = 1` for airy_dbi) | `let (bir, bii, ierr) = @slatec.zbiry(zr, zi, 0, 1, 0.0, 0.0, 0)` |

### QUADPACK

Maxima's `quad_*` functions allocate `work`/`iwork` and pass `0.0 0.0 0 0`
for `result abserr neval ier` (and `0` for `last`/`lst`):

```
pub fn dqags(f : (Double) -> Double raise, a : Double, b : Double, epsabs : Double, epsrel : Double, result : Double, abserr : Double, neval : Int, ier : Int, limit : Int, lenw : Int, last_ : Int, iwork : FixedArray[Int], work : FixedArray[Double]) -> (Double, Double, Int, Int, Int) raise
pub fn dqag(f : (Double) -> Double raise, a : Double, b : Double, epsabs : Double, epsrel : Double, key : Int, result : Double, abserr : Double, neval : Int, ier : Int, limit : Int, lenw : Int, last_ : Int, iwork : FixedArray[Int], work : FixedArray[Double]) -> (Double, Double, Int, Int, Int) raise
pub fn dqagi(f : (Double) -> Double raise, bound : Double, inf : Int, epsabs : Double, epsrel : Double, result : Double, abserr : Double, neval : Int, ier : Int, limit : Int, lenw : Int, last_ : Int, iwork : FixedArray[Int], work : FixedArray[Double]) -> (Double, Double, Int, Int, Int) raise
pub fn dqawc(f : (Double) -> Double raise, a : Double, b : Double, c : Double, epsabs : Double, epsrel : Double, result : Double, abserr : Double, neval : Int, ier : Int, limit : Int, lenw : Int, last_ : Int, iwork : FixedArray[Int], work : FixedArray[Double]) -> (Double, Double, Double, Int, Int, Int) raise
pub fn dqawf(f : (Double) -> Double raise, a : Double, omega : Double, integr : Int, epsabs : Double, result : Double, abserr : Double, neval : Int, ier : Int, limlst : Int, lst : Int, leniw : Int, maxp1 : Int, lenw : Int, iwork : FixedArray[Int], work : FixedArray[Double]) -> (Int, Double, Double, Int, Int, Int) raise
pub fn dqawo(f : (Double) -> Double raise, a : Double, b : Double, omega : Double, integr : Int, epsabs : Double, epsrel : Double, result : Double, abserr : Double, neval : Int, ier : Int, leniw : Int, maxp1 : Int, lenw : Int, last_ : Int, iwork : FixedArray[Int], work : FixedArray[Double]) -> (Int, Double, Double, Int, Int, Int) raise
pub fn dqaws(f : (Double) -> Double raise, a : Double, b : Double, alfa : Double, beta : Double, integr : Int, epsabs : Double, epsrel : Double, result : Double, abserr : Double, neval : Int, ier : Int, limit : Int, lenw : Int, last_ : Int, iwork : FixedArray[Int], work : FixedArray[Double]) -> (Double, Double, Double, Double, Int, Double, Double, Int, Int, Int) raise
pub fn dqagp(f : (Double) -> Double raise, a : Double, b : Double, npts2 : Int, points : FixedArray[Double], epsabs : Double, epsrel : Double, result : Double, abserr : Double, neval : Int, ier : Int, leniw : Int, lenw : Int, last_ : Int, iwork : FixedArray[Int], work : FixedArray[Double]) -> (Double, Double, Int, Int, Int) raise
```

| Routine | Lisp `values` (non-NIL) | MoonBit returns | `quad_*` wants |
|---------|-------------------------|-----------------|----------------|
| `dqags` | result abserr neval ier last | `(result, abserr, neval, ier, last)` | `.0 .1 .2 .3` |
| `dqag` | result abserr neval ier last | `(result, abserr, neval, ier, last)` | `.0 .1 .2 .3` |
| `dqagi` | result abserr neval ier last | `(result, abserr, neval, ier, last)` | `.0 .1 .2 .3` |
| `dqagp` | result abserr neval ier last | `(result, abserr, neval, ier, last)` | `.0 .1 .2 .3` |
| `dqawc` | c result abserr neval ier last | `(c, result, abserr, neval, ier, last)` | `.1 .2 .3 .4` |
| `dqawf` | integr result abserr neval ier lst | `(integr, result, abserr, neval, ier, lst)` | `.1 .2 .3 .4` |
| `dqawo` | integr result abserr neval ier last | `(integr, result, abserr, neval, ier, last)` | `.1 .2 .3 .4` |
| `dqaws` | a b alfa beta integr result abserr neval ier last | `(a, b, alfa, beta, integr, result, abserr, neval, ier, last)` | `.5 .6 .7 .8` |

Example (`$quad_qags`, `limit` 200, `lenw = 4*limit`):

```moonbit
let work : FixedArray[Double] = FixedArray::make(4 * limit, 0.0)
let iwork : FixedArray[Int] = FixedArray::make(limit, 0)
let (result, abserr, neval, ier, _last) = @slatec.dqags(
  integrand, a, b, epsabs, epsrel, 0.0, 0.0, 0, 0, limit, 4 * limit, 0, iwork, work,
)
// => [result, abserr, neval, ier]
```

The array sizes for the other routines are as in quadpack.lisp:
`dqawf`/`dqawo` use `leniw = limit`, `lenw = 2*leniw + 25*maxp1`;
`dqagp` uses `npts2 = 2 + #points`, a `points` array of `npts2` elements
(the singular points first), `leniw = max(limit, 3*npts2 - 2)`,
`lenw = 2*leniw - npts2`. `dqawf` takes `limlst` (default 10) and no
`epsrel`. Every other `dq*`/`dqk*` routine used internally (`dqagse`,
`dqage`, `dqagie`, `dqagpe`, `dqawce`, `dqawfe`, `dqawoe`, `dqawse`,
`dqk15`...`dqk61`, `dqk15i`, `dqk15w`, `dqc25c/f/s`, `dqcheb`, `dqelg`,
`dqpsrt`, `dqmomo`, `dqwgtc/f/s`, `dqng`, `dgtsl`) is public too.

### Error control

```
pub fn j4save(iwhich : Int, ivalue : Int, iset : Bool) -> Int
```

Returns the old value of parameter `iwhich` and stores `ivalue` when `iset`
(quadpack.lisp `quad-control`). `pub fn xermsg(librar, subrou, messg, nerr,
level)`, `xerprn`, `xersve` are available as well.

## Bit-for-bit reproduction: requirements and limits

* **Native backend.** `exp`/`log`/`pow`/trig go to the C libm, exactly what
  SBCL uses, and `sqrt` is IEEE. On wasm/js `@math` is used instead and
  results may differ in the last bits (the bit-exact tests are native-only).
* **No FMA contraction.** Clang contracts `a*b + c` into fused multiply-add
  at `-O2` on arm64, which changes roundings (one reference case fails in
  `--release` without it). `slatec/moon.pkg` passes
  `"cc-flags": "-ffp-contract=off"` for its own test executables; **any
  native executable that links this package (e.g. `cmd/main`) must add the
  same flag to its `link.native.cc-flags`** to get bit-identical results in
  release builds.
* **Machine constants** are the values f2cl-lib computes under 64-bit SBCL,
  not the textbook Fortran ones: `d1mach(3)` is SBCL's
  `double-float-epsilon` = 2^-53 + 2^-105, `d1mach(4)` twice that,
  `d1mach(5)` = `(log 2d0 10d0)`; `i1mach(9)` is `most-positive-fixnum`
  (2^62 - 1, only ever used as a double), `i1mach(12/13/15/16)` =
  -124/127/-1020/1023.
* **SBCL floating-point traps.** SBCL signals `FLOATING-POINT-OVERFLOW`,
  `DIVISION-BY-ZERO` and invalid-operation errors where MoonBit produces
  IEEE infinities/NaNs. The SLATEC routines guard against overflow
  themselves, so this matters only for integrands (Maxima's `handler-case`
  then returns the noun form; the core port has to check the integrand
  result, or the returned values, itself) and for out-of-range inputs.
* **Lisp-side f2cl bugs are not reproduced.** Calling `zbesk`, `zbesy` or
  `zbesh` *directly* with a large order (fnu around 90 and above, which
  reaches `zbunk` → `zunk1`) signals a `TYPE-ERROR` in the Lisp (a displaced
  array slice is passed where `zunk1` declares a simple array); the MoonBit
  translation computes the Fortran result. Maxima itself never hits this
  because it always passes the fractional part of the order and asks for
  `floor(order) + 1` terms.
* Fortran integers are `Int` (32-bit) where Lisp has unbounded integers;
  none of the routines computes integers anywhere near that range for valid
  input.

## Validation

* `slatec/sbcl_reference_wbtest.mbt` (generated, 1546 cases): every routine
  Maxima calls, plus `dei`, `derfc`, `dlngam`, `dgamln`, `dgamlm`, `dbie`,
  `dbsk0e`, `dbsk1e`, over many arguments (negative/small/large x, complex z
  in all quadrants, orders up to 160, `kode` 1 and 2, every QUADPACK driver
  with several integrands, all six `dqag` rules, `ier = 1` cases). The
  expected values are the IEEE bit patterns of every returned value and
  output array computed by the Lisp itself (`f2cl-lib.lisp` +
  `slatec/*.lisp` loaded into SBCL 2.6.9, and identically by the compiled
  functions inside the installed Maxima 5.50.0 image). All match, in debug
  and `--release` builds. Regenerate it with
  `python3 tools/f2cl2mbt.py --reference-test` (needs `sbcl`); 56 further
  calls are skipped because the Lisp signals an error (see above).
* `slatec/maxima_wbtest.mbt`: values printed by the reference Maxima for
  `bessel_j/y/i/k` (real and complex, small and large order), `hankel_1/2`,
  `airy_ai/bi/dai/dbi` (real and complex), `erf`, `expint`, `li[2]`,
  `gamma`, `scaled_bessel_i*`, and `quad_qags/qag/qagi/qawc/qawf/qawo/qaws/
  qagp` (including an `ier = 1` run), reproducing Maxima's glue
  computations; all agree to the last printed digit. It also checks that an
  error raised by the integrand propagates out of `dqags`.
* The XERMSG reports (`quad_qags(1/x,x,0,1)`, `ier = 6`, `dai(100.0)`
  repeated, wrapped multi-line messages, invalid `nerr`) print exactly the
  same text as Maxima.

Run with `moon test slatec` (add `--release` to check the optimized build).
