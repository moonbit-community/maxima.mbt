// Translation of share/affine/ndotsimp.lisp: simplification of
// noncommutative polynomials by the dot_simplifications rules.

///|
fn d_check_associative(a : Value, b : Value, c : Value) -> Value raise {
  let tem1 = n_dot(new_dotsimp(n_dot(a, b)), c)
  let tem2 = n_dot(a, new_dotsimp(n_dot(b, c)))
  let tem = n__(tem1, tem2)
  let tem = new_dotsimp(tem)
  if pzerop(tem).truthy() {
    tem
  } else {
    header_poly(tem)
  }
}

///|
fn ncdot_list(lis : Value) -> Value raise {
  if lis is Nil {
    Fix(1L)
  } else if cdr(lis) is Nil {
    car(lis)
  } else {
    cons(list1(q_mnctimes), lis)
  }
}

///|
/// (dot-subword #$x$ #$z.u.x.y.z.z.y$) ==> (list #$z.u$ #$y.z.z.y$))
/// (dot-subword #$x.y$ #$z.u.x.y.z.z.y$) ==> (list #$z.u$ #$z.z.y$))
/// (dot-subword #$z.u.x.y$ #$z.u.x.y.z.z.y$) ==> (list #$1$ #$z.z.y$)
fn dot_subword(small : Value, big : Value) -> Value raise {
  if atom(big) {
    if eql(big, small) {
      list([Fix(1L), Fix(1L)])
    } else {
      Nil
    }
  } else if atom(small) {
    let tem = memq(small, big)
    if tem.truthy() {
      list([
        ncdot_list(subseq(cdr(big), 0, end=length(big) - length(tem) - 1)),
        ncdot_list(cdr(tem)),
      ])
    } else {
      Nil
    }
  } else {
    let leng = length(small) - 1
    let mut v = cdr(big)
    while v is Cons(_) {
      // first part of v is equal to small
      let matches = if leng > length(v) {
        false
      } else {
        let mut ok = true
        let mut vv = v
        let mut w = cdr(small)
        while vv is Cons(_) && w is Cons(_) {
          if !equal(car(w), car(vv)) {
            ok = false
            break
          }
          vv = cdr(vv)
          w = cdr(w)
        }
        ok
      }
      if matches {
        return list([
          ncdot_list(subseq(cdr(big), 0, end=length(big) - length(v) - 1)),
          ncdot_list(nthcdr(length(cdr(small)), v)),
        ])
      }
      v = cdr(v)
    }
    Nil
  }
}

///|
/// splits into two polynomials, the first one needs no replacement and the
/// second has its leading term needing replacement
fn split_numerator(reduced : Value, rest_ : Value) -> (Value, Value) raise {
  if pzerop(rest_).truthy() {
    (reduced, Fix(0L))
  } else if poly_scalarp(rest_).truthy() {
    (n_plus(rest_, reduced), Fix(0L))
  } else if d_must_replacep(get(p__var(rest_), q_disrep)).truthy() {
    (reduced, rest_)
  } else {
    let fifth = nth(4, rest_)
    split_numerator(
      n_plus(subseq(rest_, 0, end=3), reduced),
      if fifth.truthy() {
        fifth
      } else {
        Fix(0L)
      },
    )
  }
}

///|
/// (setq-num-den num den expr) of polybas.lisp.
fn ndotsimp__num_den(expr : Value) -> (Value, Value) raise {
  if affine_polynomialp(expr).truthy() {
    (expr, Fix(1L))
  } else if rational_functionp(expr).truthy() {
    (num(expr), denom(expr))
  } else {
    fsignal(list1(Str("expr is supposed to be poly or rational-functionp")))
    |> ignore
    (Nil, Nil)
  }
}

///|
fn new_dotsimp(ratl_fun : Value) -> Value raise {
  format(t, "~%Beginning to simplify:", []) |> ignore
  sh(ratl_fun) |> ignore
  let mut expr = ratl_fun
  let mut answer : Value = Fix(0L)
  let mut mon : Value = Nil
  while true {
    if pzerop(expr).truthy() {
      return answer
    }
    let (num0, den) = ndotsimp__num_den(expr)
    let mut num = num0
    if poly_scalarp(num).truthy() {
      answer = n_plus(answer, expr)
      format(t, "~%Final answer:", []) |> ignore
      sh(answer) |> ignore
      return answer
    }
    mon = get(p__var(num), q_disrep)
    if d_must_replacep(mon).truthy() {
      if symval(q_ear_verbose_check_overlaps).truthy() {
        format(t, "~%Simplifying the worst monomial ", []) |> ignore
        dot_show(mon) |> ignore
      }
      let mut repl = simp_once_monomial(mon)
      repl = n_star(list([p__lc(num), repl]))
      let fifth = nth(4, num)
      if fifth.truthy() {
        num = n_plus(repl, fifth)
      } else {
        num = repl
      }
      expr = nred(num, den)
    } else {
      let (reduced, rest_) = split_numerator(Fix(0L), num)
      answer = n_plus(nred(reduced, den), answer)
      expr = nred(rest_, den)
      if symval(q_ear_verbose_check_overlaps).truthy() {
        format(t, "~%Simplifying the worst monomial ", []) |> ignore
        dot_show(mon) |> ignore
        format(t, " adding  to the answer", []) |> ignore
      }
    }
  }
  answer
}

///|
fn force_poly(repl : Value) -> Value raise {
  if numberp(repl) {
    repl
  } else {
    cdr(repl)
  }
}

///|
fn simp_once_monomial(monom : Value) -> Value raise {
  if atom(monom) {
    let mut tail = cdr(symval(q_d_dot_simplifications))
    while tail is Cons(_) {
      let mon = car(tail)
      let repl = cadr(tail)
      if eql(mon, monom) {
        return force_poly(repl)
      }
      tail = cddr(tail)
    }
    Nil
  } else if symval(q_d_dot_eps).truthy() &&
    {
      let tem = memq(q_d_eps, monom)
      tem.truthy() && memq(q_d_eps, cdr(tem)).truthy()
    } {
    Fix(0L)
  } else {
    let mut tail = cdr(symval(q_d_dot_simplifications))
    while tail is Cons(_) {
      let mon = car(tail)
      let repl = cadr(tail)
      let tem = dot_subword(mon, monom)
      if tem.truthy() {
        return n_dot(n_dot(car(tem), force_poly(repl)), cadr(tem))
      }
      tail = cddr(tail)
    }
    st_rat(monom)
  }
}

///|
/// ndotsimp.lisp's $DOTSIMP.  polya.lisp defines $dotsimp first (that is
/// the declared d_dotsimp), but ndotsimp.lisp is loaded after polya.lisp
/// and its definition is the one in effect after load(affine);
/// init_share_ndotsimp installs it in the function cell.
fn ndotsimp__d_dotsimp(expr : Value) -> Value raise {
  if d_listp(expr).truthy() {
    cons(list1(q_mlist), mapcar(x => funcall(q_d_dotsimp, [x]), cdr(expr)))
  } else {
    let expr = if rational_functionp(expr).truthy() ||
      affine_polynomialp(expr).truthy() {
      expr
    } else {
      new_rat(expr)
    }
    header_poly(new_dotsimp(expr))
  }
}

///|
/// Form is a non commutative polynomial, and variables a list of non
/// commutative variables.  Form is split into a list of forms of length
/// variables, so that variables.dot_factor(form) = form
fn d_dot_factor(
  form : Value,
  variables : Value,
  slot? : Value = Fix(1L),
) -> Value raise {
  // (check-arg variables $listp "macsyma list")
  if !d_listp(variables).truthy() {
    raise LispError::SimpleError("macsyma list")
  }
  let fo = st_rat(form)
  let vari = list_variables(fo)
  let n = length(variables)
  let result = make_array([n], initial=Fix(0L))
  let slot_i = to_int(slot)
  for v in vari.iter() {
    let vv = get(v, q_disrep)
    if !(vv is Sym(_) || vv is Nil) {
      let pos = position(nth(slot_i, vv), variables)
      if pos >= 0 {
        let mon = copy_list(cdr(vv))
        rplaca(nthcdr(slot_i - 1, mon), Fix(1L)) |> ignore
        aset1(
          result,
          pos,
          n_plus(
            aref1(result, pos),
            n_star(
              list([
                pcoeff(fo, v),
                st_rat(meval_star(cons(list1(q_mnctimes), mon))),
              ]),
            ),
          ),
        )
        |> ignore
      } else {
        fsignal(list1(Str("does not have a factor in slot"))) |> ignore
      }
    } else {
      let pos = position(vv, variables)
      if pos >= 0 {
        aset1(
          result,
          pos,
          n_plus(aref1(result, pos), pcoeff(fo, list([v, Fix(1L), Fix(1L)]))),
        )
        |> ignore
      }
    }
  }
  let out = Collector::new()
  for i in 1..<n {
    out.add(new_disrep(aref1(result, i)))
  }
  cons(list1(q_mlist), out.result())
}

///|
fn init_share_ndotsimp() -> Unit raise {
  defun(q_d_dotsimp, args => ndotsimp__d_dotsimp(arg(args, 0)))
}
