// Port of src/buildq.lisp: BUILDQ, a backquote-like construct for Maxima.
//
// BUILDQ([<varlist>],<expression>); the <value>s in the <varlist> are
// evaluated left to right (the syntax <atom> is equivalent to
// <atom>:<atom>), then substituted into <expression> in parallel.  If any
// <atom> appears as a single argument to the special form SPLICE inside
// <expression>, then the value associated with that <atom> must be a
// Maxima list, and it is spliced into <expression> instead of substituted.
//
// The arguments to $BUILDQ need to be protected from simplification until
// the substitutions have been carried out.

///|
/// This is modeled after SIMPMDEF, SIMPLAMBDA etc. in JM;SIMP >
fn simpbuildq(x : Value, ignored : Value, simp_flags : Value) -> Value raise {
  ignore(ignored)
  ignore(simp_flags)
  cons(list2(q_d_buildq, q_simp), cdr(x))
}

///|
fn d_buildq(form : Value) -> Value raise {
  let form = cdr(form)
  if cdr(form) is Nil || cddr(form).truthy() {
    merr("buildq: expected exactly two arguments; found ~M", [
      cons(list1(q_d_buildq), form),
    ])
  } else {
    mbuildq(car(form), cadr(form))
  }
}

///|
fn mbuildq(substitutions : Value, expression : Value) -> Value raise {
  if !d_listp(substitutions).truthy() {
    merr("buildq: first argument must be a list; found ~M", [substitutions])
    |> ignore
  }
  mbuildq_subst(
    // make a variable/value alist
    mapcar(
      form => if symbolp(form) {
        cons(form, meval(form))
      } else if eq(caar(form), q_msetq) && symbolp(cadr(form)) {
        cons(cadr(form), meval(caddr(form)))
      } else {
        merr(
          "buildq: variable must be a symbol or an assignment to a symbol; found ~M",
          [form],
        )
      },
      cdr(substitutions),
    ),
    expression,
  )
}

///|
/// This performs the substitutions for the variables in the expressions.
/// It tries to be smart and only copy what list structure it has to. The
/// first arg is an alist of pairs: (<variable> . <value>); the second arg
/// is the Maxima expression to substitute into.
fn mbuildq_subst(alist : Value, expression : Value) -> Value raise {
  let mut new_car : Value = Nil
  if atom(expression) {
    return mbuildq_associate(expression, alist)
  } else if atom(car(expression)) {
    new_car = mbuildq_associate(car(expression), alist)
  } else if mbuildq_splice_associate(expression, alist).truthy() {
    // if the expression is a legal SPLICE, this clause is taken. a SPLICE
    // should never occur here.  It corresponds to `,@form
    merr("splice: encountered 'splice' in an unexpected place: ~M", [expression])
    |> ignore
  } else if atom(caar(expression)) {
    new_car = mbuildq_associate(caar(expression), alist)
    if eq(new_car, caar(expression)) {
      new_car = car(expression)
    } else if atom(new_car) {
      // Be careful to verbify a string before substituting into the
      // operator.
      let op = if stringp(new_car) {
        let v = d_verbify(new_car)
        if v.truthy() {
          v
        } else {
          new_car
        }
      } else {
        new_car
      }
      new_car = cons(op, cdar(expression))
    } else {
      return list_star([
        cons(q_mqapply, cdar(expression)),
        new_car,
        mbuildq_subst(alist, cdr(expression)),
      ])
    }
  } else {
    new_car = mbuildq_splice_associate(car(expression), alist)
    if new_car.truthy() {
      return append(cdr(new_car), mbuildq_subst(alist, cdr(expression)))
    }
    new_car = mbuildq_subst(alist, car(expression))
  }
  let new_cdr = mbuildq_subst(alist, cdr(expression))
  if eq(new_car, car(expression)) &&
    eq(new_cdr, cdr(expression)) {
    expression
  } else {
    cons(new_car, new_cdr)
  }
}

///|
/// This function returns the appropriate thing to substitute for an atom
/// appearing inside a backquote.  If it's not in the varlist, it's the atom
/// itself.
fn mbuildq_associate(atom_ : Value, alist : Value) -> Value raise {
  if !symbolp(atom_) {
    return atom_
  }
  let form = assq(atom_, alist)
  if form.truthy() {
    return cdr(form)
  }
  // trying to match a nounified substitution variable
  let form = assq(d_verbify(atom_), alist)
  if form.truthy() {
    let v = cdr(form)
    if atom(v) {
      d_nounify(v)
    } else if memq(
        caar(v),
        list([q_mquote, q_mlist, q_mprog, q_mprogn, q_lambda]),
      ).truthy() {
      // list gotten from the parser.
      list2(list1(q_mquote), v)
    } else {
      // ((<verb> ...) ...)  ==>  ((<noun> ...) ...)
      cons(cons(d_nounify(caar(v)), cdar(v)), cdr(v))
    }
  } else {
    atom_
  }
}

///|
/// This function decides whether the SPLICE is one of ours or not. The
/// SPLICE is ours if it has exactly one symbolic argument and that arg
/// appears in the current varlist. If it's one of ours, this function
/// returns the list it's bound to (an MLIST, whose cdr is spliced in);
/// otherwise it returns nil.
fn mbuildq_splice_associate(expression : Value, alist : Value) -> Value raise {
  if eq(caar(expression), q_d_splice) &&
    cdr(expression).truthy() &&
    cddr(expression) is Nil {
    let match_ = assq(cadr(expression), alist)
    if match_ is Nil {
      Nil
    } else if !d_listp(cdr(match_)).truthy() {
      merr("buildq: 'splice' must return a list, but ~M returned: ~M~%", [
        expression,
        cdr(match_),
      ])
    } else {
      cdr(match_)
    }
  } else {
    Nil
  }
}

///|
fn init_buildq() -> Unit raise {
  putprop(q_d_buildq, q_simpbuildq, q_operators) |> ignore
  putprop(q_p_buildq, q_simpbuildq, q_operators) |> ignore
}
