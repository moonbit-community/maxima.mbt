// Port of share/contrib/simplifying.lisp (Stavros Macrakis, 2007-2019):
// Maxima-level user-defined simplifying functions.
//
// For example, suppose we want to write a step function stepfn(x)
// which is 0 for x<0 and 1 for x>0.
//
// /* Define simplifying function */
// simp_stepfn(x):=
//   block([prederror:false],
//      if is(x<=0)=true then 0
//      elseif is(x>0)=true then 1
//      else simpfuncall('stepfn,x))$
// /* Declare stepfn to be simplifying */
// simplifying('stepfn,'simp_stepfn)$

///|
fn defined_functionp(ex : Value) -> Value raise {
  if ex is Nil {
    Nil
  } else if symbolp(ex) {
    if fboundp(ex) ||
      safe_mgetl(ex, list2(q_mexpr, q_mmacro)).truthy() {
      t
    } else {
      Nil
    }
  } else if !atom(ex) && eq(caar(ex), q_lambda) {
    t
  } else {
    Nil
  }
}

///|
/// macro (mwarn str &rest args):
/// `(mtell ,(concatenate 'string "Warning: " str) ,@args)
fn mwarn(str : Value, args : Value) -> Value raise {
  let s = match str {
    Str(s) => s
    _ => princ_to_string(str)
  }
  mtell(cons(Str("Warning: " + s), args))
}

///|
/// Declare a user Maxima function to be a simplifying function
/// simplifying(f,g) -- uses g as the simplifier
/// simplifying(f,false) -- removes simplifying property
///
/// You can override built-in simplifiers, but it is not recommended
fn d_simplifying(f : Value, simplifier : Value) -> Value raise {
  if !symbolp(f) {
    merror(Str("Simplifying function ~M must be a symbol"), list1(f)) |> ignore
  }
  if simplifier.truthy() && !defined_functionp(simplifier).truthy() {
    mwarn(Str("simplifier function ~M is not defined"), list1(simplifier))
    |> ignore
  }
  if get(f, q_operators).truthy() && !get(f, q_user_simplifying).truthy() {
    mwarn(
      Str("~M is overriding built-in simplifier for ~M"),
      list2(simplifier, f),
    )
    |> ignore
  }
  setf_get(f, q_user_simplifying, simplifier) |> ignore
  setf_get(
    f,
    q_operators,
    if simplifier.truthy() {
      q_user_simplifying
    } else {
      Nil
    },
  )
  |> ignore
  f
}

///|
/// Create the expression fun(args...) and mark it as simplified.
/// Thus, simpfuncall(sin,0) => sin(0), not 0, but resimplifying with
/// expand(simpfuncall(sin,0)) does simplify to 0.
fn d_simpfuncall(fun : Value, args : Value) -> Value raise {
  simpfunmake(fun, args)
}

///|
fn d_simpfunmake(fun : Value, args : Value) -> Value raise {
  simpfunmake(
    fun,
    if d_listp(args).truthy() {
      cdr(args)
    } else {
      merror(Str("Bad second argument to `simpfunmake': ~M"), list1(args))
    },
  )
}

///|
fn simpfunmake(fun : Value, args : Value) -> Value raise {
  // Code copied from (updated) $funmake
  if !(
      (
        symbolp(fun) &&
        !member(fun, list([t, Nil, q_d__pcte, q_d__pcti, q_d__pctpi])).truthy()
      ) ||
      d_subvarp(fun).truthy() ||
      (stringp(fun) && getopr0(fun).truthy()) ||
      (!atom(fun) && eq(caar(fun), q_lambda))
    ) {
    merror(Str("Bad first argument to `simpfuncall/make': ~M"), list1(fun))
    |> ignore
  }
  simpcons(getopr(fun), args)
}

///|
fn simpcons(op : Value, args : Value) -> Value raise {
  if symbolp(op) {
    cons(list2(op, q_simp), args)
  } else {
    cons(list2(q_mqapply, q_simp), cons(op, args))
  }
}

///|
/// The generic simplifying function for user simplification functions
fn user_simplifying(
  l : Value,
  ignore_ : Value,
  simpflag : Value,
) -> Value raise {
  ignore(ignore_)
  let op = caar(l)
  let simplifier = get(op, q_user_simplifying)
  // args are (re)simplified *outside* the simplification fnc
  let args = mapcar(i => simpcheck(i, simpflag), cdr(l))
  // args have already been resimplified if necessary
  with_special(q_dosimp, Nil, () => if defined_functionp(simplifier).truthy() {
    mapply(simplifier, args, op)
  } else {
    simpcons(op, args)
  })
}

///|
fn init_share_simplifying() -> Unit raise {

}
