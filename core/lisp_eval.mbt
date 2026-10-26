// The Lisp evaluator: runs Lisp code at run time (load of .lisp files,
// :lisp, to_lisp(), ?-calls of Lisp macros and lambda expressions, and the
// code produced by the Maxima-to-Lisp translator).
//
// Design: a form is compiled once into a tree of MoonBit closures
// (`LeCode`), which then run against a runtime frame (`LeFrame`).
// - Lexical variables live in frame slots; the compile-time environment
//   (`LeEnv`) maps a variable to (frame depth, slot). Every LET-like form
//   with lexical variables, and every function activation, has its own
//   frame; closures capture the frame chain.
// - Special variables use the symbol value cells and the runtime's
//   shallow BIND/UNBIND. A variable is special when it is declared so
//   locally, proclaimed by DEFVAR & co., one of Maxima's specials
//   (lisp_eval_specials.mbt) or named *LIKE-THIS*.
// - Functions: a call (f ...) funcalls f's function cell, so ported
//   functions and interpreted ones (DEFUN installs an LFunc in the cell)
//   call each other freely.
// - Macros: the MACRO-FUNCTION property of the symbol (DEFMACRO sets it;
//   this is also where the ported code keeps its expanders), else the
//   built-in expanders written in MoonBit (`le__builtin_macros`).
// - Non-local exits: BLOCK/RETURN-FROM, TAGBODY/GO and CATCH/THROW use the
//   runtime's LispError::ReturnFrom/Go/Throw with fresh tags per
//   activation, so ported and interpreted code interoperate.
// - Multiple values: a values register (`le__mv`). VALUES and the
//   multiple-valued CL functions set it; a call clears it before invoking
//   the callee; forms compiled in "tail" mode (the last form of an
//   interpreted function body, the argument of MULTIPLE-VALUE-BIND, ...)
//   leave it valid. Ported functions return their primary value only.

///|
priv struct LeFrame {
  vals : Array[Value]
  up : LeFrame?
}

///|
type LeCode = (LeFrame) -> Value raise

///|
/// Size of a runtime frame, known once its scope is compiled.
priv struct LeFInfo {
  mut size : Int
}

///|
priv struct LeBlockInfo {
  mut used : Bool
  mv : Bool
}

///|
/// Compile-time lexical environment.
priv enum LeEnv {
  Top
  Frame(LeFInfo, LeEnv)
  Var(Symbol, Int, LeEnv)
  Special(Symbol, LeEnv)
  SymMacro(Symbol, Value, LeEnv)
  Fun(Symbol, Int, LeEnv)
  Mac(Symbol, Value, LeEnv)
  Block(Value, Int, LeBlockInfo, LeEnv)
  Tags(Array[Value], Array[Int], Int, LeBlockInfo, LeEnv)
}

///|
/// The multiple values register.
let le__mv : Ref[Array[Value]?] = Ref(None)

///|
/// The compile-time environment of the macro expansion in progress (for
/// MACROEXPAND with an &environment argument).
let le__cur_env : Ref[LeEnv] = Ref(Top)

///|
let le__q_lambda : Value = sym("lambda")

///|
let le__q_declare : Value = sym("declare")

///|
let le__q_special : Value = sym("special")

///|
let le__q_amp_optional : Value = sym("&optional")

///|
let le__q_amp_rest : Value = sym("&rest")

///|
let le__q_amp_body : Value = sym("&body")

///|
let le__q_amp_key : Value = sym("&key")

///|
let le__q_amp_aux : Value = sym("&aux")

///|
let le__q_amp_allow : Value = sym("&allow-other-keys")

///|
let le__q_amp_whole : Value = sym("&whole")

///|
let le__q_amp_env : Value = sym("&environment")

///|
let le__q_macro_function : Value = sym("macro-function")

///|
let le__q_setf : Value = sym("setf")

// ---------------------------------------------------------------------------
// Errors

///|
fn le__error(msg : String) -> Value raise {
  raise LispError::SimpleError(msg)
}

///|
fn le__program_error(msg : String) -> Value raise {
  raise LispError::Condition(intern("program-error"), msg, Nil)
}

///|
fn le__unbound(s : Value) -> Value raise {
  raise LispError::Condition(
    intern("unbound-variable"),
    "The variable " + prin1_to_string(s) + " is unbound.",
    s,
  )
}

///|
fn le__undefined_function(s : Value) -> Value raise {
  raise LispError::Condition(
    intern("undefined-function"),
    "The function " + prin1_to_string(s) + " is undefined.",
    s,
  )
}

// ---------------------------------------------------------------------------
// Special variables

///|
/// Names proclaimed special at run time (DEFVAR, DECLAIM, ...).
let le__proclaimed : Set[String] = Set::new()

///|
fn le__special_p(s : Symbol) -> Bool {
  let n = s.name
  if le__proclaimed.contains(n) || le__maxima_specials().contains(n) {
    return true
  }
  // *earmuffs*
  n.length() > 2 && n.has_prefix("*") && n.has_suffix("*")
}

///|
fn le__proclaim_special(s : Value) -> Unit {
  match s {
    Sym(sy) => le__proclaimed.add(sy.name)
    _ => ()
  }
}

// ---------------------------------------------------------------------------
// Environment lookup

///|
priv enum LeVarLoc {
  Lex(Int, Int)
  Dyn
  SMac(Value)
}

///|
fn le__lookup_var(env : LeEnv, s : Symbol) -> LeVarLoc {
  let mut e = env
  let mut depth = 0
  while true {
    match e {
      Top => return Dyn
      Frame(_, p) => {
        depth += 1
        e = p
      }
      Var(v, slot, p) => {
        if v.id == s.id {
          return Lex(depth, slot)
        }
        e = p
      }
      Special(v, p) => {
        if v.id == s.id {
          return Dyn
        }
        e = p
      }
      SymMacro(v, x, p) => {
        if v.id == s.id {
          return SMac(x)
        }
        e = p
      }
      Fun(_, _, p) | Mac(_, _, p) | Block(_, _, _, p) | Tags(_, _, _, _, p) =>
        e = p
    }
  }
  Dyn
}

///|
priv enum LeFunLoc {
  LexFun(Int, Int)
  LocalMac(Value)
  GlobalFun
}

///|
fn le__lookup_fun(env : LeEnv, s : Symbol) -> LeFunLoc {
  let mut e = env
  let mut depth = 0
  while true {
    match e {
      Top => return GlobalFun
      Frame(_, p) => {
        depth += 1
        e = p
      }
      Fun(v, slot, p) => {
        if v.id == s.id {
          return LexFun(depth, slot)
        }
        e = p
      }
      Mac(v, x, p) => {
        if v.id == s.id {
          return LocalMac(x)
        }
        e = p
      }
      Var(_, _, p) | Special(_, p) | SymMacro(_, _, p) | Block(_, _, _, p) =>
        e = p
      Tags(_, _, _, _, p) => e = p
    }
  }
  GlobalFun
}

///|
/// Allocate a slot in the nearest frame. Returns the slot index.
fn le__alloc_slot(env : LeEnv) -> Int raise {
  let mut e = env
  while true {
    match e {
      Top => {
        le__error("internal: no frame to allocate a slot") |> ignore
        return 0
      }
      Frame(info, _) => {
        let k = info.size
        info.size += 1
        return k
      }
      Var(_, _, p) | Special(_, p) | SymMacro(_, _, p) | Fun(_, _, p) | Mac(_, _, p) =>
        e = p
      Block(_, _, _, p) | Tags(_, _, _, _, p) => e = p
    }
  }
  0
}

///|
fn le__frame_at(f : LeFrame, depth : Int) -> LeFrame {
  let mut fr = f
  for _ in 0..<depth {
    match fr.up {
      Some(u) => fr = u
      None => ()
    }
  }
  fr
}

///|
fn le__new_frame(info : LeFInfo, up : LeFrame) -> LeFrame {
  { vals: Array::make(info.size, Value::Nil), up: Some(up) }
}

// ---------------------------------------------------------------------------
// Multiple values

///|
/// After running code compiled in tail mode: all the values it produced.
fn le__values_of(v : Value) -> Array[Value] {
  match le__mv.val {
    Some(a) => {
      le__mv.val = None
      if a.length() == 0 {
        if v is Nil {
          a
        } else {
          [v]
        }
      } else if eq(a[0], v) {
        a
      } else {
        [v]
      }
    }
    None => [v]
  }
}

///|
/// Return values from a builtin: set the register, return the primary.
fn le__values(vals : Array[Value]) -> Value {
  if vals.length() == 1 {
    le__mv.val = None
    vals[0]
  } else {
    le__mv.val = Some(vals)
    if vals.length() == 0 {
      Nil
    } else {
      vals[0]
    }
  }
}

///|
/// Wrap code that does not produce multiple values for a tail context.
fn le__single(c : LeCode, mv : Bool) -> LeCode {
  if mv {
    f => {
      let v = c(f)
      le__mv.val = None
      v
    }
  } else {
    c
  }
}

// ---------------------------------------------------------------------------
// Body parsing: docstrings and declarations

///|
/// Split a body into its SPECIAL declarations and the remaining forms.
fn le__parse_body(body : Value, doc_ok : Bool) -> (Array[Symbol], Value) {
  let specials : Array[Symbol] = []
  let mut b = body
  while true {
    match b {
      Cons({ car: Cons({ car: hd, cdr: specs }), cdr: rest }) if eq(
          hd, le__q_declare,
        ) => {
        for spec in specs.iter() {
          if eq(car(spec), le__q_special) {
            for v in cdr(spec).iter() {
              if v is Sym(s) {
                specials.push(s)
              }
            }
          }
        }
        b = rest
      }
      Cons({ car: Str(_), cdr: Cons(_) as rest }) if doc_ok => b = rest
      _ => break
    }
  }
  (specials, b)
}

///|
fn le__sym_in(s : Symbol, l : Array[Symbol]) -> Bool {
  for x in l {
    if x.id == s.id {
      return true
    }
  }
  false
}

///|
/// Add Special entries for declared specials that are not bound by the
/// form itself (free declarations).
fn le__add_free_specials(
  env : LeEnv,
  specials : Array[Symbol],
  bound : Array[Symbol],
) -> LeEnv {
  let mut e = env
  for s in specials {
    if !le__sym_in(s, bound) {
      e = Special(s, e)
    }
  }
  e
}

// ---------------------------------------------------------------------------
// The compiler

///|
fn le__const(v : Value) -> LeCode {
  _f => v
}

///|
/// Compile a form. `mv`: the code is in a tail context whose multiple
/// values are wanted, so it must leave the values register valid.
fn le__comp(form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  match form {
    Sym(s) =>
      if s.constant || s.name == "t" {
        le__single(le__const(form), mv)
      } else {
        le__single(le__comp_var(s, form, env), mv)
      }
    Cons({ car: Sym(s) as head, cdr: args }) =>
      le__comp_compound(s, head, args, form, env, mv)
    Cons({ car: Cons({ car: lam, .. }) as fn_, cdr: args }) if eq(
        lam, le__q_lambda,
      ) => {
      let fc = le__comp_function(fn_, env)
      le__comp_call_code(fc, args, env, mv)
    }
    Cons(_) => {
      le__error("illegal function call: " + prin1_to_string(form)) |> ignore
      le__const(Nil)
    }
    _ => le__single(le__const(form), mv)
  }
}

///|
fn le__comp_var(s : Symbol, form : Value, env : LeEnv) -> LeCode raise {
  match le__lookup_var(env, s) {
    Lex(0, i) => f => f.vals[i]
    Lex(1, i) =>
      f => match f.up {
        Some(u) => u.vals[i]
        None => Nil
      }
    Lex(d, i) => f => le__frame_at(f, d).vals[i]
    Dyn =>
      _f => if s.bound {
        s.value
      } else {
        le__unbound(form)
      }
    SMac(x) => le__comp(x, env, false)
  }
}

///|
/// Code that stores a value into a variable.
fn le__comp_setvar(
  s : Symbol,
  env : LeEnv,
  vc : LeCode,
) -> LeCode raise {
  match le__lookup_var(env, s) {
    Lex(0, i) =>
      f => {
        let v = vc(f)
        f.vals[i] = v
        v
      }
    Lex(d, i) =>
      f => {
        let v = vc(f)
        le__frame_at(f, d).vals[i] = v
        v
      }
    Dyn => {
      let sv = Value::Sym(s)
      f => {
        let v = vc(f)
        set(sv, v) |> ignore
        v
      }
    }
    SMac(x) => {
      // (setf expansion value): evaluate the value first into a temp
      le__comp(list3(le__q_setf, x, list2(sym("quote"), Nil)), env, false)
      |> ignore
      let place = x
      f => {
        let v = vc(f)
        le__eval_in(list3(le__q_setf, place, list2(sym("quote"), v)), env, f)
      }
    }
  }
}

///|
/// Evaluate a form at run time in a given compile-time environment (used
/// for rare paths such as SETQ of a symbol macro).
fn le__eval_in(form : Value, env : LeEnv, f : LeFrame) -> Value raise {
  (le__comp(form, env, false))(f)
}

///|
fn le__comp_progn(body : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let codes : Array[LeCode] = []
  let forms = list_to_array(body)
  for i, x in forms {
    codes.push(le__comp(x, env, mv && i == forms.length() - 1))
  }
  match codes.length() {
    0 => le__single(le__const(Nil), mv)
    1 => codes[0]
    2 => {
      let a = codes[0]
      let b = codes[1]
      f => {
        a(f) |> ignore
        b(f)
      }
    }
    3 => {
      let a = codes[0]
      let b = codes[1]
      let c = codes[2]
      f => {
        a(f) |> ignore
        b(f) |> ignore
        c(f)
      }
    }
    n =>
      f => {
        for i in 0..<(n - 1) {
          (codes[i])(f) |> ignore
        }
        (codes[n - 1])(f)
      }
  }
}

///|
/// Compile an argument list into an array of codes.
fn le__comp_args(args : Value, env : LeEnv) -> Array[LeCode] raise {
  let r : Array[LeCode] = []
  for a in args.iter() {
    r.push(le__comp(a, env, false))
  }
  r
}

///|
fn le__eval_args(codes : Array[LeCode], f : LeFrame) -> Array[Value] raise {
  let n = codes.length()
  let a = Array::make(n, Value::Nil)
  for i in 0..<n {
    a[i] = (codes[i])(f)
  }
  a
}

///|
/// Call a function value (computed by `fc`) on the arguments.
fn le__comp_call_code(
  fc : LeCode,
  args : Value,
  env : LeEnv,
  mv : Bool,
) -> LeCode raise {
  let ac = le__comp_args(args, env)
  let c : LeCode = f => {
    let fv = fc(f)
    let a = le__eval_args(ac, f)
    le__mv.val = None
    le__funcall(fv, a)
  }
  ignore(mv)
  c
}

///|
/// FUNCALL with CL semantics: function values and fbound symbols; a
/// lambda expression list is also accepted.
fn le__funcall(fv : Value, a : Array[Value]) -> Value raise {
  match fv {
    Func(lf) => (lf.call)(a)
    Sym({ func: Some(lf), .. }) => (lf.call)(a)
    Sym(_) => le__undefined_function(fv)
    Cons({ car: lam, .. }) if eq(lam, le__q_lambda) =>
      le__funcall(le__closure_of_lambda(fv, Top, None), a)
    Nil => le__undefined_function(fv)
    _ => le__error("funcall: not a function: " + prin1_to_string(fv))
  }
}

///|
/// The CL functions compiled inline (when the function cell still holds
/// the evaluator's own definition): name -> (arity, operation).
fn le__inline_op(name : String, n : Int) -> ((Value, Value) -> Value raise)? {
  match (name, n) {
    ("+", 2) => Some((a, b) => num_add(a, b))
    ("-", 2) => Some((a, b) => num_sub(a, b))
    ("*", 2) => Some((a, b) => num_mul(a, b))
    ("<", 2) => Some((a, b) => lbool(num_lt(a, b)))
    (">", 2) => Some((a, b) => lbool(num_gt(a, b)))
    ("<=", 2) => Some((a, b) => lbool(num_le(a, b)))
    (">=", 2) => Some((a, b) => lbool(num_ge(a, b)))
    ("=", 2) => Some((a, b) => lbool(num_eq(a, b)))
    ("eq", 2) => Some((a, b) => lbool(eq(a, b)))
    ("eql", 2) => Some((a, b) => lbool(eql(a, b)))
    ("equal", 2) => Some((a, b) => lbool(equal(a, b)))
    ("cons", 2) => Some((a, b) => cons(a, b))
    ("1+", 1) => Some((a, _) => one_plus(a))
    ("1-", 1) => Some((a, _) => one_minus(a))
    ("car", 1) => Some((a, _) => car_strict(a))
    ("cdr", 1) => Some((a, _) => cdr_strict(a))
    ("cadr", 1) => Some((a, _) => cadr(a))
    ("cddr", 1) => Some((a, _) => cddr(a))
    ("caar", 1) => Some((a, _) => caar(a))
    ("cdar", 1) => Some((a, _) => cdar(a))
    ("null", 1) | ("not", 1) => Some((a, _) => lbool(a is Nil))
    ("atom", 1) => Some((a, _) => lbool(!(a is Cons(_))))
    ("consp", 1) => Some((a, _) => lbool(a is Cons(_)))
    _ => None
  }
}

///|
/// The function cells of the inlined operations as the evaluator set them
/// up (an inline call checks that the cell has not been redefined).
let le__inline_cells : Map[Int, LFunc] = Map::new()

///|
fn le__comp_global_call(
  s : Symbol,
  head : Value,
  args : Value,
  env : LeEnv,
) -> LeCode raise {
  let nargs = length(args)
  match (le__inline_op(s.name, nargs), le__inline_cells.get(s.id)) {
    (Some(op), Some(orig)) => {
      let a0 = le__comp(car(args), env, false)
      let slow = le__comp_global_call_slow(s, head, args, env)
      if nargs == 1 {
        return f => match s.func {
            Some(lf) if physical_equal(lf, orig) => {
              let x = a0(f)
              le__mv.val = None
              op(x, Nil)
            }
            _ => slow(f)
          }
      }
      let a1 = le__comp(cadr(args), env, false)
      return f => match s.func {
          Some(lf) if physical_equal(lf, orig) => {
            let x = a0(f)
            let y = a1(f)
            le__mv.val = None
            op(x, y)
          }
          _ => slow(f)
        }
    }
    _ => ()
  }
  le__comp_global_call_slow(s, head, args, env)
}

///|
fn le__comp_global_call_slow(
  s : Symbol,
  head : Value,
  args : Value,
  env : LeEnv,
) -> LeCode raise {
  let ac = le__comp_args(args, env)
  match ac.length() {
    0 =>
      _f => {
        le__mv.val = None
        match s.func {
          Some(lf) => (lf.call)([])
          None => le__undefined_function(head)
        }
      }
    1 => {
      let a0 = ac[0]
      f => {
        let x = a0(f)
        le__mv.val = None
        match s.func {
          Some(lf) => (lf.call)([x])
          None => le__undefined_function(head)
        }
      }
    }
    2 => {
      let a0 = ac[0]
      let a1 = ac[1]
      f => {
        let x = a0(f)
        let y = a1(f)
        le__mv.val = None
        match s.func {
          Some(lf) => (lf.call)([x, y])
          None => le__undefined_function(head)
        }
      }
    }
    _ =>
      f => {
        let a = le__eval_args(ac, f)
        le__mv.val = None
        match s.func {
          Some(lf) => (lf.call)(a)
          None => le__undefined_function(head)
        }
      }
  }
}

///|
/// The global macro expander of a symbol, if any.
fn le__global_macro(s : Symbol) -> Value? {
  let p = get(Sym(s), le__q_macro_function)
  if p.truthy() {
    return Some(p)
  }
  None
}

///|
/// Expand a macro form with an expander function value.
fn le__call_expander(expander : Value, form : Value, env : LeEnv) -> Value raise {
  let saved = le__cur_env.val
  le__cur_env.val = env
  defer {
    le__cur_env.val = saved
  }
  match expander {
    Cons(_) => le__funcall(le__closure_of_lambda(expander, Top, None), [form, Nil])
    _ => funcall(expander, [form, Nil])
  }
}

///|
fn le__comp_compound(
  s : Symbol,
  head : Value,
  args : Value,
  form : Value,
  env : LeEnv,
  mv : Bool,
) -> LeCode raise {
  // special operators
  match le__special_forms().get(s.name) {
    Some(h) =>
      // a local function may not shadow a special operator, but flet of a
      // name that is a macro here is fine; check lexical functions first
      // only for our macro-like special forms.
      return h(args, form, env, mv)
    None => ()
  }
  match le__lookup_fun(env, s) {
    LexFun(d, i) => {
      let fc : LeCode = f => le__frame_at(f, d).vals[i]
      return le__comp_call_code(fc, args, env, mv)
    }
    LocalMac(expander) =>
      return le__comp(le__call_expander(expander, form, env), env, mv)
    GlobalFun => ()
  }
  match le__global_macro(s) {
    Some(expander) =>
      return le__comp(le__call_expander(expander, form, env), env, mv)
    None => ()
  }
  match le__builtin_macros().get(s.name) {
    Some(expander) => return le__comp(expander(form, env), env, mv)
    None => ()
  }
  le__comp_global_call(s, head, args, env)
}

// ---------------------------------------------------------------------------
// Macro expansion (for MACROEXPAND and SETF)

///|
/// Expand a form once if it is a macro form: (expansion, expanded?).
fn le__macroexpand_1(form : Value, env : LeEnv) -> (Value, Bool) raise {
  match form {
    Cons({ car: Sym(s), .. }) => {
      if le__special_forms().contains(s.name) {
        return (form, false)
      }
      match le__lookup_fun(env, s) {
        LexFun(_, _) => return (form, false)
        LocalMac(expander) =>
          return (le__call_expander(expander, form, env), true)
        GlobalFun => ()
      }
      match le__global_macro(s) {
        Some(expander) => return (le__call_expander(expander, form, env), true)
        None => ()
      }
      match le__builtin_macros().get(s.name) {
        Some(expander) => (expander(form, env), true)
        None => (form, false)
      }
    }
    Sym(s) =>
      match le__lookup_var(env, s) {
        SMac(x) => (x, true)
        _ => (form, false)
      }
    _ => (form, false)
  }
}

///|
fn le__macroexpand(form : Value, env : LeEnv) -> (Value, Bool) raise {
  let mut f = form
  let mut any = false
  while true {
    let (g, ex) = le__macroexpand_1(f, env)
    if !ex {
      break
    }
    any = true
    f = g
  }
  (f, any)
}

// ---------------------------------------------------------------------------
// Top level

///|
/// Compile and run a form in the null lexical environment.
fn le__eval_toplevel(form : Value) -> Value raise {
  let info = { size: 0 }
  let env = Frame(info, Top)
  let code = le__comp(form, env, true)
  let fr = { vals: Array::make(info.size, Value::Nil), up: None }
  code(fr)
}

///|
/// Evaluate a top-level form of a file being loaded: PROGN, LOCALLY and
/// EVAL-WHEN bodies are processed form by form, so that a macro defined by
/// one form is used by the next.
fn le__eval_file_form(form : Value) -> Value raise {
  match form {
    Cons({ car: Sym({ name: "progn", .. }), cdr: body }) => {
      let mut v : Value = Nil
      for x in body.iter() {
        v = le__eval_file_form(x)
      }
      v
    }
    Cons({ car: Sym({ name: "eval-when", .. }), cdr: Cons({ car: sit, cdr: body }) }) =>
      if le__eval_when_executes(sit, false) {
        let mut v : Value = Nil
        for x in body.iter() {
          v = le__eval_file_form(x)
        }
        v
      } else {
        Nil
      }
    Cons({ car: Sym(s), .. }) if !le__special_forms().contains(s.name) &&
      (le__global_macro(s) is Some(_) || le__builtin_macros().contains(s.name)) => {
      let (g, ex) = le__macroexpand_1(form, Top)
      if ex {
        le__eval_file_form(g)
      } else {
        le__eval_toplevel(form)
      }
    }
    _ => le__eval_toplevel(form)
  }
}

///|
/// Does an EVAL-WHEN with situations `sit` run its body? At top level of a
/// file being loaded :load-toplevel also counts.
fn le__eval_when_executes(sit : Value, toplevel : Bool) -> Bool {
  for x in sit.iter() {
    match x {
      Sym({ name: ":execute" | "eval", .. }) => return true
      Sym({ name: ":load-toplevel" | "load", .. }) if toplevel => return true
      _ => ()
    }
  }
  false
}
