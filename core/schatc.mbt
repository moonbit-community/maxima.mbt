// Port of src/schatc.lisp: SCHATCHEN, the pattern matcher (M2) described in
// Chapter 3 of J. Moses' thesis "Symbolic Integration" (MIT-LCS-TR-047).
// "Schatchen" is Yiddish for "matchmaker".
//
// The answer alist lives in the special *SCHATC-ANS*; context markers (NIL)
// and *LOOP markers delimit what RESTORE, RESTORE1 and RESTORE2 undo.
// Entries of the form (z . (cdr z)) record destructive deletions (SAV&DEL)
// so that the expression can be repaired when a match fails.
//
// A variable in a pattern is (name pred arg2 ... argn); a pattern with a
// mode is in prefix form, e.g. A*x with A a number coefficient of TIMES is
// ((coefft) (a number) x).  See the long comment in schatc.lisp for the
// description of COEFFT, COEFFP, COEFFPT, COEFFTT, COEFFPP, LOOP, ZEPOW and
// the VAR* switches (SET, UVAR, COEFFPT).

///|
fn schatc__ans() -> Value {
  symval(q_ear_schatc_ans)
}

///|
/// macro push-context: (push nil *schatc-ans*)
fn push_context() -> Value raise {
  set(q_ear_schatc_ans, cons(Nil, schatc__ans()))
}

///|
/// macro push-loop-context
fn push_loop_context() -> Value raise {
  let a = schatc__ans()
  rplacd(a, cons(q_n_starloop, cdr(a)))
}

///|
/// macro preserve: remember (z . (cdr z)) so that a deletion can be undone.
fn preserve(z : Value) -> Value raise {
  let a = schatc__ans()
  rplacd(a, cons(cons(z, cdr(z)), cdr(a)))
}

///|
/// macro add-to: push the binding (var . val) on the answer.
fn add_to(var_ : Value, val : Value) -> Value raise {
  let a = schatc__ans()
  rplacd(a, cons(cons(var_, val), cdr(a)))
}

///|
/// macro var-pat
fn var_pat(x : Value) -> Value raise {
  lbool(atom(car(x)))
}

///|
fn schatc__var_pat(x : Value) -> Bool {
  atom(car(x))
}

// VARIOUS SIMPLE PATTERNS

///|
fn free1(a : Value) -> Value raise {
  if pzerop(a) is Nil {
    free(a, symval(q_var))
  } else {
    Nil
  }
}

///|
fn not_zero_free(a : Value, var_ : Value) -> Value raise {
  with_special(q_var, var_, () => free1(a))
}

///|
fn linear_star(e : Value, var_ : Value) -> Value raise {
  with_special(q_var, var_, fn() raise {
    let n = d_ratcoef(e, var_)
    if free(n, var_) is Nil {
      return Nil
    }
    let a = simplus(
      list([list1(q_mplus), e, list([list1(q_mtimes), Fix(-1L), n, var_])]),
      Fix(1L),
      Nil,
    )
    if free(a, var_).truthy() {
      cons(a, n)
    } else {
      Nil
    }
  })
}

///|
fn dvcoe(e : Value, pat : Value, args : Value) -> Value raise {
  m1(d_ratsimp(list([list1(q_mtimes), e, args]), Nil), pat)
}

///|
/// Match the (maxima) expression E with the pattern P.
fn schatchen(e : Value, p : Value) -> Value raise {
  m2(e, p)
}

///|
fn m2(e : Value, p : Value) -> Value raise {
  with_specials([(q_ear_schatc_ans, list1(Nil)), (q_ear_splist, Nil)], fn() raise {
    if m1(copy_tree(e), p) is Nil {
      Nil
    } else if cdr(schatc__ans()) is Nil {
      t
    } else {
      cdr(schatc__ans())
    }
  })
}

///|
fn sav_ampdel(x : Value) -> Value raise {
  preserve(x) |> ignore
  rplacd(x, cddr(x))
}

///|
fn m1(e : Value, p : Value) -> Value raise {
  if equal(e, p) {
    t
  } else if atom(p) {
    Nil
  } else if schatc__var_pat(p) {
    push_context() |> ignore
    if testa(p, e, Nil).truthy() {
      restore1()
    } else {
      restore()
    }
  } else if atom(caar(p)) {
    let op = caar(p)
    if memq(q_simp, cdar(p)).truthy() {
      alike1(e, p)
    } else if eq(op, q_mplus) || eq(op, q_mtimes) {
      loopp(e, p)
    } else if eq(op, q_mexpt) || eq(op, q_zepow) {
      zepow(e, p, t)
    } else if !atom(e) && eq(caar(e), op) {
      eachp(e, p)
    } else if eq(op, q_coefft) {
      coefft(e, p, t)
    } else if eq(op, q_coeffpt) {
      coeffpt(e, p, t)
    } else if eq(op, q_coeffp) {
      coeffp(e, p, t)
    } else if eq(op, q_coefftt) {
      coefftt(e, cadr(p), t, q_mtimes)
    } else if eq(op, q_coeffpp) {
      coefftt(e, cadr(p), t, q_mplus)
    } else {
      Nil
    }
  } else if schatc__var_pat(caar(p)) {
    // HAIRY OPERATOR MATCHING SCHEME
    if atom(e) {
      Nil // NO OPERATOR TO MATCH
    } else {
      push_context() |> ignore // BIND THE CONTEXT
      if testa(caar(p), car(e), Nil).truthy() { // TRY IT
        if eq(caar(e), q_mplus) || eq(caar(e), q_mtimes) { // CHECK FOR COMMUTIVITY
          if loopp(e, cons(car(e), cdr(p))).truthy() {
            restore1()
          } else {
            restore()
          }
        } else if eachp(e, p).truthy() {
          restore1()
        } else {
          restore()
        }
      } else {
        restore()
      }
    }
  } else {
    Nil
  }
}

///|
fn loopp(e : Value, p : Value) -> Value raise {
  let mut e = e
  let mut x : Value = Nil
  e = if atom(e) {
    list2(car(p), e)
  } else if !eq(caar(p), caar(e)) {
    if symval(q_ear_schatfactor).truthy() &&
      eq(caar(e), q_mplus) &&
      ({
        x = d_factor(e)
        mtimesp(x).truthy()
      }) {
      x
    } else {
      list2(car(p), e)
    }
  } else {
    e
  }
  push_context() |> ignore
  let mut z = p
  while true {
    // loop
    z = cdr(z)
    if z is Nil {
      return if cdr(e) is Nil { restore1() } else { restore() }
    }
    x = e
    // l5
    while true {
      if cdr(x) is Nil {
        let ident = opident(caar(p))
        if ident.truthy() && m1(ident, car(z)).truthy() {
          break
        } else {
          return restore()
        }
      } else if atom(car(z)) || schatc__var_pat(car(z)) {
        if m1(cadr(x), car(z)).truthy() {
          sav_ampdel(x) |> ignore
          break
        }
      } else if eq(caaar(z), q_coefft) {
        if coefft(e, car(z), Nil).truthy() {
          break
        } else {
          return restore()
        }
      } else if eq(caaar(z), q_coeffp) {
        if coeffp(e, car(z), Nil).truthy() {
          break
        } else {
          return restore()
        }
      } else if eq(caaar(z), q_coeffpt) {
        if coeffpt(e, car(z), Nil).truthy() {
          break
        } else {
          return restore()
        }
      } else if eq(caaar(z), q_coefftt) {
        if coefftt(e, cadar(z), Nil, q_mtimes).truthy() {
          break
        } else {
          return restore()
        }
      } else if eq(caaar(z), q_coeffpp) {
        if coefftt(e, cadar(z), Nil, q_mplus).truthy() {
          break
        } else {
          return restore()
        }
      } else if eq(caaar(z), q_mexpt) || eq(caaar(z), q_zepow) {
        if zepow(cadr(x), car(z), t).truthy() {
          sav_ampdel(x) |> ignore
          break
        }
      } else if eq(caaar(z), q_loop) {
        if sch_loop(e, cdar(z)).truthy() {
          break
        } else {
          return restore()
        }
      } else if m1(cadr(x), car(z)).truthy() {
        sav_ampdel(x) |> ignore
        break
      }
      x = cdr(x)
    }
  }
  Nil
}

///|
/// IND = T MEANS AN INTERNAL CALL (USUALLY FROM LOOPP)
fn coeffp(e : Value, p : Value, ind : Value) -> Value raise {
  let mut e = e
  push_context() |> ignore
  if (
      mplusp(e) is Nil &&
      ({
        e = list2(list1(q_mplus), e)
        true
      })
    ) ||
    ind.truthy() ||
    cddr(e) is Nil {
    // WITH IND SET, OR E = (PLUS <EXPR>): USE COEFFPORT
    coeffport(e, p, Fix(0L), ind)
  } else if cddr(p) is Nil && schatc__var_pat(cadr(p)) {
    // P = ((COEFFP) (<VAR> <PRED> . . .)) SO CALL TESTA
    if testa(cadr(p), e, Nil).truthy() {
      if mplusp(e).truthy() {
        preserve(e) |> ignore
        rplacd(e, Nil) |> ignore
        t
      } else {
        merr("COEFFP: incorrect arguments; E=~M, P=~M, IND=~M", [e, p, ind])
      }
    } else {
      Nil
    }
  } else {
    let mut x = e
    while true {
      if cdr(x) is Nil {
        return if m1(Fix(0L), p).truthy() { restore2() } else { restore() }
      }
      if coeffp(cadr(x), p, t).truthy() {
        sav_ampdel(x) |> ignore
        return restore2()
      }
      x = cdr(x)
    }
    Nil
  }
}

///|
fn coefft(e : Value, p : Value, ind : Value) -> Value raise {
  let mut e = e
  push_context() |> ignore
  if ind is Nil && !atom(e) && (eq(caar(e), q_mplus) || eq(caar(e), q_mtimes)) {
    let mut x = e
    while true {
      if cdr(x) is Nil {
        return if m1(Fix(1L), p).truthy() { restore2() } else { restore() }
      }
      if coefft(cadr(x), p, t).truthy() {
        sav_ampdel(x) |> ignore
        return restore2()
      }
      x = cdr(x)
    }
    Nil
  } else if mplusp(e).truthy() && cddr(e).truthy() {
    if symval(q_ear_schatfactor).truthy() &&
      ({
        e = d_factor(e)
        mtimesp(e).truthy()
      }) {
      coeffport(e, p, Fix(1L), ind)
    } else {
      restore()
    }
  } else {
    coeffport(
      if mtimesp(e).truthy() {
        e
      } else {
        list2(list1(q_mtimes), e)
      },
      p,
      Fix(1L),
      ind,
    )
  }
}

///|
fn coeffport(e : Value, p : Value, ident : Value, ind : Value) -> Value raise {
  let mut z = cddr(p)
  while true {
    if z is Nil {
      return coeffret(e, cadr(p), ident, ind)
    }
    let mut x = e
    // l: EACH TIME HERE WE HAVE CDR'D DOWN THE EXP.
    while true {
      if cdr(x) is Nil {
        if m1(ident, car(z)) is Nil {
          return restore()
        }
      } else if atom(car(z)) || schatc__var_pat(car(z)) {
        ()
      } else if eq(caaar(z), q_coefftt) {
        if coefftt(e, cadar(z), Nil, q_mtimes) is Nil {
          return coeffret(e, p, ident, ind)
        }
      } else if eq(caaar(z), q_coeffpp) {
        if coefftt(e, cadar(z), Nil, q_mplus) is Nil {
          return coeffret(e, p, ident, ind)
        }
      }
      if cdr(x) is Nil {
        break
      } else if m1(cadr(x), car(z)).truthy() {
        sav_ampdel(x) |> ignore
        break
      } else {
        x = cdr(x)
      }
    }
    z = cdr(z)
  }
  Nil
}

///|
fn coeffret(e : Value, p : Value, ident : Value, ind : Value) -> Value raise {
  if cdr(e) is Nil {
    if testa(p, ident, Nil).truthy() {
      if ind.truthy() {
        restore1()
      } else {
        restore2()
      }
    } else {
      restore()
    }
  } else if testa(p, if cddr(e).truthy() { copy_list(e) } else { cadr(e) }, Nil).truthy() {
    if ind.truthy() {
      restore1()
    } else {
      preserve(e) |> ignore
      rplacd(e, Nil) |> ignore
      restore2()
    }
  } else {
    restore()
  }
}

///|
/// THE PATTERN LIST (P) MUST BE OF VAR-PATTERNS
fn coeffpt(e : Value, p : Value, ind : Value) -> Value raise {
  push_context() |> ignore
  let mut z = if mplusp(e).truthy() { e } else { list2(list1(q_mplus), e) }
  // THIS ROUTINE IS THE ONE WHICH PUTS MOST OF THE THE GARBAGE ON ANS.
  // IT CANNOT USE THE *SPLIST* HACK BECAUSE IT COULD BE USING MANY
  // DIFFERENT VARIABLES ALTHOUGH THOUGHT THE FIRST IS THE ONLY ONE.
  let zz = cons(list1(q_coefft), cdr(p))
  while true {
    if cdr(z) is Nil {
      z = findit(
        if eq(caadr(p), q_var_star) {
          car(cddr(cadr(p)))
        } else {
          caadr(p)
        },
      )
      let q : Value = if z is Nil {
        Fix(0L)
      } else if cdr(z) is Nil {
        car(z)
      } else {
        simplus(cons(list1(q_mplus), z), Fix(1L), Nil)
      }
      // WHICH BECOMES A SUM AND MIGHT BE RESET
      let fl = if z.truthy() && cdr(z).truthy() { q_coeffpt } else { Nil }
      return if testa(cadr(p), q, fl) is Nil {
        restore()
      } else if ind.truthy() {
        restore1()
      } else {
        restore2() |> ignore
        q
      }
    }
    // THIS IS THE DO BODY
    if m1(cadr(z), zz) is Nil {
      z = cdr(z)
    } else {
      sav_ampdel(z) |> ignore
    }
  }
  Nil
}

///|
/// FL=NIL INDICATES A RECURSIVE CALL SO ANS SHOULD NOT BE MARKED
fn zepow(e : Value, p : Value, fl : Value) -> Value raise {
  let mut e = e
  if fl.truthy() {
    push_context() |> ignore
  }
  if atom(e) {
    if equal(e, Fix(1L)) {
      if !(m1(Fix(0L), caddr(p)).truthy() || m1(Fix(1L), cadr(p)).truthy()) {
        restore()
      } else {
        restore1()
      }
    } else if equal(e, Fix(0L)) {
      if m1(Fix(0L), cadr(p)) is Nil {
        restore()
      } else {
        restore1()
      }
    } else if m1(e, cadr(p)).truthy() && m1(Fix(1L), caddr(p)).truthy() {
      restore1()
    } else {
      restore()
    }
  } else {
    // (AND *SCHATFACTOR* (MPLUSP E) (SETQ E ($FACTOR E)) NIL): a clause
    // that is never selected but may change E.
    if symval(q_ear_schatfactor).truthy() && mplusp(e).truthy() {
      e = d_factor(e)
    }
    if eq(caar(e), q_mtimes) && mexptp(cadr(e)).truthy() {
      let mut b = cadadr(e)
      let mut x = caddr(cadr(e))
      let mut ee = cddr(e)
      while true {
        if ee is Nil {
          // OK NOW LETS TRY AGAIN
          return zepow(
            list3(list1(q_mexpt), simplifya(b, t), simplifya(x, t)),
            p,
            Nil,
          )
        }
        if mexptp(car(ee)).truthy() {
          if alike1(cadar(ee), b).truthy() {
            x = simplus(list3(list1(q_mplus), x, caddar(ee)), Fix(1L), Nil)
          } else if alike1(caddar(ee), x).truthy() {
            b = simptimes(list3(list1(q_mtimes), b, cadar(ee)), Fix(1L), Nil)
          } else {
            let z = d_divide(x, caddar(ee), Nil)
            let r = caddr(z)
            if numberp(r) && zerop(r) {
              b = simptimes(
                list3(
                  list1(q_mtimes),
                  b,
                  list3(
                    list1(q_mexpt),
                    cadar(ee),
                    list3(list1(q_mtimes), caddar(ee), cadr(z)),
                  ),
                ),
                Fix(1L),
                Nil,
              )
            } else {
              return restore()
            }
          }
        } else if alike1(b, car(ee)).truthy() {
          x = simplus(list3(list1(q_mplus), Fix(1L), x), Fix(1L), t)
        } else {
          return restore()
        }
        ee = cdr(ee)
      }
      Nil
    } else if (
        eq(caar(e), q_mexpt) &&
        m1(cadr(e), cadr(p)).truthy() &&
        m1(caddr(e), caddr(p)).truthy()
      ) ||
      (m1(e, cadr(p)).truthy() && m1(Fix(1L), caddr(p)).truthy()) {
      restore1()
    } else {
      restore()
    }
  }
}

///|
fn eachp(e : Value, p : Value) -> Value raise {
  if length(e) == length(p) {
    push_context() |> ignore
    let mut p = p
    let mut e = cdr(e)
    while true {
      if e is Nil {
        return restore1()
      }
      if m1(car(e), cadr(p)) is Nil {
        return restore()
      }
      p = cdr(p)
      e = cdr(e)
    }
    Nil
  } else {
    Nil
  }
}

///|
fn sch_loop(e : Value, lp : Value) -> Value raise {
  push_context() |> ignore
  push_loop_context() |> ignore
  let mut x = lp
  let mut z = e
  let mut y : Value = Nil // Y A PSEUDO SAVE
  while true {
    if m1(cadr(z), car(x)) is Nil { // DIDN'T MATCH
      z = cdr(z) // NEXT ARG FOR LOOP
      if cdr(z).truthy() {
        ()
      } else if eq(x, lp) {
        return restore()
      } else {
        x = caar(y)
        z = cdar(y)
        y = cdr(y)
        set(q_ear_schatc_ans, cdr(schatc__ans())) |> ignore
        pop_loop_context() |> ignore
      }
    } else {
      y = cons(cons(x, z), y)
      sav_ampdel(z) |> ignore
      x = cdr(x)
      if x is Nil {
        return restore2()
      } else {
        push_loop_context() |> ignore
        z = e
      }
    }
  }
  Nil
}

///|
/// OPIND IS MPLUS OR MTIMES
fn coefftt(
  exp_ : Value,
  pat : Value,
  ind : Value,
  opind : Value,
) -> Value raise {
  let mut exp_ = exp_
  push_context() |> ignore
  if atom(exp_) || (ind.truthy() && !eq(caar(exp_), opind)) {
    exp_ = list2(list1(opind), exp_)
  }
  set(q_ear_splist, cons(car(pat), symval(q_ear_splist))) |> ignore // SAVE VAR NAME HERE
  let mut z = exp_
  let mut res : Value = Nil
  while true {
    if cdr(z) is Nil {
      set(q_ear_splist, cdr(symval(q_ear_splist))) |> ignore // KILL NAME SAVED
      if res.truthy() {
        res = if cdr(res).truthy() { cons(list1(opind), res) } else { car(res) }
        if eq(car(pat), q_var_star) && memq(q_set, cadr(pat)).truthy() {
          add_to(caddr(pat), set(caddr(pat), simplifya(res, Nil))) |> ignore
        } else {
          add_to(car(pat), simplifya(res, Nil)) |> ignore
        }
        return if ind.truthy() { restore1() } else { restore2() }
      } else if testa(pat, opident(opind), Nil) is Nil {
        return restore()
      } else if ind.truthy() {
        return restore1()
      } else {
        return restore2()
      }
    }
    if testa(pat, cadr(z), Nil).truthy() {
      res = cons(cadr(z), res)
      sav_ampdel(z) |> ignore
    } else {
      z = cdr(z)
    }
  }
  Nil
}

// THE RESTORE FUNCTIONS RESTORE THE SPEC-VAR ANS AND RETURN TRUE OR FALSE
// AS FOLLOWS
// RESTORE - FALSE
// RESTORE1 - TRUE AND CLEARS UP ANS
// RESTORE2 - TRUE AND CLEARS OFF *LOOP INDICATORS; DOES NOT FIX UP THE
//            EXPRESSION AND IS THUS TO BE USED ONLY INTERNALLY

///|
fn restore() -> Value raise {
  let mut y = cdr(schatc__ans())
  while y.truthy() {
    if eq(car(y), q_n_starloop) {
      rplaca(y, cadr(y)) |> ignore
      rplacd(y, cddr(y)) |> ignore
    } else if car(y) is Nil {
      set(q_ear_schatc_ans, y) |> ignore
      return Nil
    } else if !atom(caar(y)) {
      rplacd(caar(y), cdar(y)) |> ignore
    }
    y = cdr(y)
  }
  Nil
}

///|
fn restore1() -> Value raise {
  let mut y = schatc__ans()
  let mut l : Value = Nil // L IS A LIST OF VAR'S NOTED
  while true {
    if cdr(y) is Nil {
      return t
    }
    if cadr(y) is Nil { // END OF CONTEXT
      rplacd(y, cddr(y)) |> ignore // SPLICE OUT THE CONTEXT MARKER
      return t
    } else if !atom(caadr(y)) { // FIXUP NECESSARY
      rplacd(caadr(y), cdadr(y)) |> ignore
      rplacd(y, cddr(y)) |> ignore
    } else if memq(car(y), l).truthy() { // THIS VAR HAS ALREADY BEEN SEEN
      rplacd(y, cddr(y)) |> ignore // SO SPLICE IT OUT TO KEEP ANS CLEAN
    } else {
      y = cdr(y)
      l = cons(caar(y), l)
    }
  }
  t
}

///|
fn restore2() -> Value raise {
  let mut y = cdr(schatc__ans())
  while true {
    if cdr(y) is Nil {
      return t
    }
    if eq(cadr(y), q_n_starloop) {
      rplacd(y, cddr(y)) |> ignore
    } else if cadr(y) is Nil {
      rplacd(y, cddr(y)) |> ignore
      return t
    }
    y = cdr(y)
  }
  t
}

///|
fn pop_loop_context() -> Value raise {
  let y = schatc__ans()
  while true {
    if eq(cadr(y), q_n_starloop) {
      return Nil
    }
    if !atom(caadr(y)) {
      rplacd(caadr(y), cdadr(y)) |> ignore
    }
    rplacd(y, cddr(y)) |> ignore
  }
  Nil
}

// WHEN THE CAR OF ALA IS VAR* THE CADR IS A LIST OF THE VARIOUS SWITCHES
// WHICH MAY BE SET.
// UVAR- INDICATES THIS SHOULD MATCH SOMETHING WHICH IS ALREADY ON ANS.
// SET - ACTUALLY SET THIS VARIABLE TO ITS VALUE IF IT MATCHES.
// COEFFPT - SPECIAL ARGUMENT IF IN COEFFPT.

///|
fn testa(ala : Value, exp_ : Value, b : Value) -> Value raise {
  if eq(car(ala), q_mvar_star) {
    testa_star(ala, exp_, t)
  } else if eq(car(ala), q_var_star) {
    let mut z = cadr(ala)
    let mut ala = cddr(ala)
    let mut y : Value = Nil
    let mut set_ = false
    let mut uvar = false
    while true {
      if z is Nil {
        y = if uvar { m1(exp_, y) } else { testa_star(ala, exp_, Nil) }
        return if y is Nil {
          Nil
        } else if set_ {
          set(car(ala), exp_)
        } else {
          y
        }
      }
      if eq(car(z), q_set) {
        set_ = true
      } else if eq(car(z), q_uvar) {
        y = cdr(assoc_equal(car(ala), schatc__ans()))
        if y.truthy() {
          uvar = true
        }
      } else if eq(car(z), q_coeffpt) {
        if eq(b, q_coeffpt) {
          ala = cadr(z)
        }
        z = cdr(z)
      } else {
        merr("TESTA: invalid switch ~M in pattern.", [car(z)]) |> ignore
      }
      z = cdr(z)
    }
    Nil
  } else {
    testa_star(ala, exp_, Nil)
  }
}

///|
fn schatc__applicable(f : Value) -> Bool {
  fboundp(f) || functionp(f)
}

///|
/// ALA IS THE PREDICATE LIST (VAR PREDFN ARG2 ARG3 ARG4 . . .)
fn testa_star(ala : Value, exp_ : Value, loc : Value) -> Value raise {
  let mut exp_ = exp_
  let pred = cadr(ala)
  let ok = if eq(pred, q_freevar) {
    let var_ = symval(q_var)
    if eq(var_, q_n_starnovar) {
      lbool(equal(exp_, Fix(1L)))
    } else {
      free(exp_, var_)
    }
  } else if eq(pred, q_numberp) {
    mnump(exp_)
  } else if eq(pred, q_true) {
    t
  } else if eq(pred, q_linear_star) {
    exp_ = linear_star(exp_, caddr(ala))
    exp_
  } else if loc is Nil {
    if atom(pred) {
      if schatc__applicable(pred) {
        apply(pred, findthem(exp_, cddr(ala)))
      } else if mget(pred, q_mexpr).truthy() {
        mapply(pred, findthem(exp_, cddr(ala)), pred)
      } else {
        Nil
      }
    } else if eq(car(pred), q_lambda) ||
      eq(car(pred), q_function) ||
      eq(car(pred), q_n_starfunction) ||
      eq(car(pred), q_quote) {
      // THE LAMBDA IS HERE ONLY BECAUSE OF SIN!!!
      apply(matcom__lisp_function(pred), findthem(exp_, cddr(ala)))
    } else {
      eval_pred(pred, car(ala), exp_)
    }
  } else {
    Nil
  }
  if ok.truthy() {
    let m = memq(car(ala), symval(q_ear_splist))
    if m.truthy() {
      m
    } else {
      add_to(car(ala), exp_)
    }
  } else if loc.truthy() && atom(pred) && schatc__applicable(pred) {
    let vars = car(ala)
    let mut qs = vars
    let mut vs = apply(pred, findthem(exp_, cddr(ala)))
    while qs.truthy() && vs.truthy() {
      let q = car(qs)
      if memq(q, symval(q_ear_splist)) is Nil {
        add_to(q, car(vs)) |> ignore
      }
      qs = cdr(qs)
      vs = cdr(vs)
    }
    vars
  } else {
    Nil
  }
}

///|
/// Evaluate the Lisp form EXP with %VAR bound to VALUE.  The port has no
/// general Lisp evaluator; the form is run by the small evaluator used for
/// compiled match programs (see matcom.mbt).
fn eval_pred(exp_ : Value, p_var : Value, value : Value) -> Value raise {
  progv(list1(p_var), list1(value), () => matcom__lisp_eval(exp_))
}

///|
fn findthem(exp_ : Value, args : Value) -> Value raise {
  cons(
    exp_,
    mapcar(
      fn(q) {
        if atom(q) {
          let v = cdr(assq(q, schatc__ans()))
          if v.truthy() {
            v
          } else if symbolp(q) && boundp(q) && symval(q).truthy() {
            // Evaluate a symbol which has a value.
            symval(q)
          } else {
            // Otherwise return the symbol.
            q
          }
        } else {
          q
        }
      },
      args,
    ),
  )
}

///|
fn findit(a : Value) -> Value raise {
  let mut y = schatc__ans()
  let mut z : Value = Nil
  while true {
    if cdr(y) is Nil || cadr(y) is Nil {
      return z
    }
    if eq(caadr(y), a) {
      z = nconc(z, list1(cdadr(y)))
      rplacd(y, cddr(y)) |> ignore
    } else {
      y = cdr(y)
    }
  }
  z
}

///|
fn sch_replace(dict : Value, exp1 : Value) -> Value raise {
  with_special(q_dict, dict, () => replac(exp1))
}

///|
fn replac(exp1 : Value) -> Value raise {
  if exp1 is Nil {
    Nil
  } else if !atom(exp1) {
    if eq(car(exp1), q_eval) {
      simplifya(matcom__lisp_eval(replac(cadr(exp1))), Nil)
    } else if eq(car(exp1), q_quote) {
      cadr(exp1)
    } else {
      let w1 = mapcar(x => replac(x), cdr(exp1))
      if equal(w1, cdr(exp1)) {
        exp1
      } else {
        simplifya(cons(list1(caar(exp1)), w1), t)
      }
    }
  } else if numberp(exp1) {
    exp1
  } else {
    let w1 = assq(exp1, symval(q_dict))
    if w1.truthy() {
      cdr(w1)
    } else {
      exp1
    }
  }
}
