// Port of share/linearalgebra/matrixexp.lisp.
//
// Innocent looking problems, such as
// matrixexp(matrix([x,1,0],[1,1,1],[0,1,1])), generate huge expressions.
// To avoid errors such as "quotient by polynomial of higher degree" the code
// (1) sets gcd to spmod and algebraic to true, (2) always gives ratsimp nil
// as its optional second argument, and (3) sets ratvars to an empty list at
// the start of most functions.

///|
/// Convert all subexpressions of `e` of the form `(-1)^rational number`, to
/// rectangular form by temporarily binding $domain to $complex and calling
/// `$rectform`.
fn rect_minus_one_power(e : Value) -> Value raise {
  if mexptp(e).truthy() &&
    eql(second(e), Fix(-1L)) &&
    d_ratnump(third(e)).truthy() {
    with_special(q_d_domain, q_d_complex, () => d_rectform(e))
  } else if consp(e) {
    fapply(caar(e), mapcar(x => rect_minus_one_power(x), cdr(e)))
  } else {
    e
  }
}

///|
fn final_simp(e : Value, depth? : Value = Fix(4L)) -> Value raise {
  with_specials(
    [(q_d_ratsimpexpons, t), (q_d_algebraic, t), (q_d_radexpand, t)],
    () => {
      let ee = d_resimplify(
        rect_minus_one_power(d_factor(d_ratsimp(e, list1(Nil)))),
      )
      if alike1(e, ee).truthy() || num_le(depth, Fix(0L)) {
        ee
      } else {
        final_simp(ee, depth=num_sub(depth, Fix(1L)))
      }
    },
  )
}

///|
/// Standard environment and function for simplification in this package.
fn matrixexp_simp(e : Value, depth? : Value = Fix(4L)) -> Value raise {
  // A parallel LET: EE is computed before the bindings take effect.
  let ee = d_resimplify(
    d_factor(d_ratsimp(rect_minus_one_power(e), list1(Nil))),
  )
  with_specials(
    [
      (q_d_algebraic, t),
      (q_d_ratsimpexpons, t),
      (q_d_domain, q_d_complex),
      (q_d_radexpand, Nil),
      (q_d_m1pbranch, t),
      (q_d_ratvarswitch, t),
    ],
    () => if alike1(e, ee).truthy() || num_le(depth, Fix(0L)) {
      ee
    } else {
      matrixexp_simp(ee, depth=num_sub(depth, Fix(1L)))
    },
  )
}

///|
fn d_spectral_rep(mat : Value) -> Value raise {
  d_require_square_matrix(mat, q_d_first, q_d_spectral_rep) |> ignore
  d_require_unblockedmatrix(mat, q_d_first, q_d_spectral_rep) |> ignore
  let mat = d_ratdisrep(mat)
  let z = gensym()
  let n = d_length(d_args(mat))
  with_specials(
    [
      (q_d_ratmx, Nil),
      (q_d_domain, q_d_complex),
      (q_d_gcd, q_d_spmod),
      (q_d_algebraic, t),
      (q_d_resultant, q_d_subres),
      (q_d_ratfac, Nil),
      (q_d_matrix_element_mult, Str("*")),
      (q_d_matrix_element_add, Str("+")),
    ],
    () => {
      let mut p = d_newdet(sub(mat, mul2(z, d_ident(n))))
      if oddp(n) {
        p = mul2(Fix(-1L), p)
      }
      // p1 = (z - z1)(z - z2) ... (z - zk), where z1 thru zk are the
      // distinct zeros of p.
      let p1 = d_first(
        d_divide(p, d_gcd(p, d_diff(list2(p, z)), list1(z)), list1(z)),
      )
      let mut p2 = d_resultant(p1, d_diff(list2(p1, z)), z)
      if !d_constantp(p2).truthy() && !alike1(Fix(0L), p2).truthy() {
        p2 = d_sqfr(p2)
        if mminusp(p2).truthy() {
          p2 = mul2(Fix(-1L), p2)
        }
        p2 = if mtimesp(p2).truthy() { margs(p2) } else { list1(p2) }
        p2 = mapcar(s => if mexptp(s).truthy() { nth(1, s) } else { s }, p2)
        p2 = fapply(q_mtimes, p2)
        mtell(
          list2(Str("Proviso: assuming ~:M ~%"), ftake(q_mnotequal, [p2, Fix(0L)])),
        )
        |> ignore
      }
      let mut sp = d_solve(p, varl=z)
      sp = mapcar(s => d_rhs(s), cdr(sp))
      if !eql(n, num_sum(list_to_array(cdr(symval(q_d_multiplicities))))) {
        merr("Unable to find the spectrum", []) |> ignore
      }
      let res = matrixexp_simp(
        ncpower(sub(mul2(z, d_ident(n)), mat), Fix(-1L)),
      )
      let mut m = length(sp)
      let mut proj : Value = Nil
      for i in 0..<m {
        let zi = nth(i, sp)
        let ord = nth(i + 1, symval(q_d_multiplicities))
        proj = cons(
          matrix_map(
            lfunc("residue", args => rational_residue(args[0], z, zi, p, ord)),
            res,
          ),
          proj,
        )
      }
      proj = nreverse(proj)
      m = length(proj)
      let mut remainder = mat
      for i in 0..<m {
        remainder = sub(remainder, mul2(nth(i, sp), nth(i, proj)))
      }
      remainder = matrixexp_simp(remainder)
      // When nilpotent-p can determine that remainder is nilpotent, return
      // the spectral representation; otherwise merror.
      if nilpotent_p(remainder).truthy() {
        ftake(q_mlist, [fapply(q_mlist, sp), fapply(q_mlist, proj), remainder])
      } else {
        merr("Unable to find the spectral representation", [])
      }
    },
  )
}

///|
/// Return T if the Maxima matrix MAT is nilpotent, NIL otherwise.  Uses
/// repeated multiplication up to the matrix dimension.
fn nilpotent_p(mat : Value) -> Value raise {
  let n = d_length(mat)
  let zero = d_zeromatrix(n, n)
  let mut power = mat
  // If already zero, nilpotent
  if alike1(matrixexp_simp(mat), zero).truthy() {
    return t
  }
  // Try powers mat^2, mat^3, ..., mat^n
  for _ in 0..<to_int(n) {
    power = ncmul2(power, mat)
    if alike1(matrixexp_simp(power), zero).truthy() {
      return t
    }
  }
  Nil
}

///|
/// When mat is a square matrix, return exp(mat * x). The second argument is
/// optional and it defaults to 1.
fn d_matrixexp(mat : Value, x? : Value = Fix(1L)) -> Value raise {
  let n = d_length(d_args(mat))
  with_specials(
    [
      (q_d_ratmx, Nil),
      (q_d_gcd, q_d_spmod),
      (q_d_matrix_element_mult, Str("*")),
      (q_d_matrix_element_add, Str("+")),
      (q_d_domain, q_d_complex),
    ],
    () => {
      d_ratvars(Nil) |> ignore
      d_require_square_matrix(mat, q_d_first, q_d_matrixexp) |> ignore
      d_require_unblockedmatrix(mat, q_d_first, q_d_matrixexp) |> ignore
      let mat = d_spectral_rep(mat)
      let mut sp = d_first(mat)
      let p = share_lu__second(mat)
      sp = fapply(
        q_mlist,
        mapcar(s => ftake(q_mexpt, [q_d__pcte, mul2(s, x)]), cdr(sp)),
      )
      let d = mul2(x, share_lu__third(mat))
      let id = d_ident(n)
      let mut f = id
      let n = num_add(n, Fix(1L))
      // Horner scheme
      let mut i : Value = Fix(0L)
      while num_lt(i, n) {
        f = add2(id, div(ncmul2(d, f), num_sub(n, i)))
        i = num_add(i, Fix(1L))
      }
      matrixexp_simp(ncmul2(ncmul2(sp, p), f))
    },
  )
}

///|
/// Let f(var) = expr.  This function returns f(mat), where 'mat' is a square
/// matrix.
fn require_lambda(e : Value, n : Value, pos : Value, fun_name : Value) -> Value raise {
  let ok = consp(e) &&
    consp(car(e)) &&
    eq(q_lambda, mop(e)) &&
    length(e) == 3 &&
    d_listp(nth(1, e)).truthy() &&
    cdr(nth(1, e)).truthy() &&
    num_eq(n, int(length(cdr(nth(1, e))))) &&
    every(
      s => symbolp(s) || d_subvarp(s).truthy(),
      cdr(nth(1, e)),
    )
  if ok {
    list2(cdr(nth(1, e)), nth(2, e))
  } else {
    merr("The ~:M argument to `~:M' must be a lambda form with ~:M variable(s)", [
      pos, fun_name, n,
    ])
  }
}

///|
fn d_matrixfun(lamexpr : Value, mat : Value) -> Value raise {
  let z = gensym()
  let n = d_length(d_args(mat))
  let ff = with_specials(
    [
      (q_d_gcd, q_d_spmod),
      (q_d_ratmx, Nil),
      (q_d_matrix_element_mult, Str("*")),
      (q_d_matrix_element_add, Str("+")),
      (q_d_domain, q_d_complex),
    ],
    () => {
      let mut f : Value = Fix(0L)
      d_require_square_matrix(mat, q_d_second, q_d_matrixfun) |> ignore
      d_require_unblockedmatrix(mat, q_d_second, q_d_matrixfun) |> ignore
      let mut expr = require_lambda(lamexpr, Fix(1L), q_d_first, q_d_matrixfun)
      let var_ = nth(0, nth(0, expr))
      expr = nth(1, expr)
      expr = d_substitute(z, var_, expr~)
      let mat = d_spectral_rep(mat)
      let mut sp = d_first(mat)
      let p = share_lu__second(mat)
      let d = share_lu__third(mat)
      let mut di = d_ident(n)
      sp = cdr(sp)
      let mut i : Value = Fix(0L)
      let nn = num_add(n, Fix(1L))
      while num_lt(i, nn) {
        let e = expr
        f = add2(
          f,
          ncmul2(
            di,
            ncmul2(fapply(q_mlist, mapcar(s => maxima_substitute(s, z, e), sp)), p),
          ),
        )
        di = ncmul2(di, d)
        expr = div(d_diff(list2(expr, z)), factorial(num_add(i, Fix(1L))))
        i = num_add(i, Fix(1L))
      }
      f
    },
  )
  final_simp(ff)
}

///|
/// Return the residue of the rational expression e with respect to the
/// variable var at the point pt.  Assumptions: (1) the denominator of e
/// divides ker, (2) e is a rational expression, (3) ker is a polynomial,
/// (4) pt is a zero of ker and ord is its order.
fn rational_residue(
  e : Value,
  var_ : Value,
  pt : Value,
  ker : Value,
  ord : Value,
) -> Value raise {
  let f = sub(var_, pt)
  with_specials([(q_d_gcd, q_d_spmod), (q_d_algebraic, t), (q_d_ratfac, Nil)], () => {
    let mut e = sratsimp(e)
    let mut p = d_num(e)
    let q = d_denom(e)
    p = mul2(p, d_quotient(list3(ker, q, var_)))
    e = div(p, d_quotient(list3(ker, power(f, ord), var_)))
    matrixexp_simp(
      maxima_substitute(
        pt,
        var_,
        div(
          d_diff(list3(e, var_, num_sub(ord, Fix(1L)))),
          factorial(num_sub(ord, Fix(1L))),
        ),
      ),
    )
  })
}

///|
fn init_share_matrixexp() -> Unit raise {
  d_put(q_d_matrixexp, Fix(2026L), q_d_version) |> ignore
}
