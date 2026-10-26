// Lisp evaluator: special operators.

///|
type LeSpecialHandler = (Value, Value, LeEnv, Bool) -> LeCode raise

///|
fn le__make_special_table() -> Map[String, LeSpecialHandler] {
  {
  "quote": le__sf_quote,
  "function": le__sf_function,
  "setq": le__sf_setq,
  "if": le__sf_if,
  "progn": le__sf_progn,
  "let": le__sf_let,
  "let*": le__sf_let_star,
  "flet": le__sf_flet,
  "labels": le__sf_labels,
  "macrolet": le__sf_macrolet,
  "symbol-macrolet": le__sf_symbol_macrolet,
  "block": le__sf_block,
  "return-from": le__sf_return_from,
  "tagbody": le__sf_tagbody,
  "go": le__sf_go,
  "catch": le__sf_catch,
  "throw": le__sf_throw,
  "unwind-protect": le__sf_unwind_protect,
  "eval-when": le__sf_eval_when,
  "locally": le__sf_locally,
  "the": le__sf_the,
  "multiple-value-call": le__sf_mv_call,
  "multiple-value-prog1": le__sf_mv_prog1,
  "multiple-value-bind": le__sf_mv_bind,
  "progv": le__sf_progv,
  "load-time-value": le__sf_load_time_value,
  "declare": le__sf_declare,
  "defun": le__sf_defun,
  "defmacro": le__sf_defmacro,
  "destructuring-bind": le__sf_destructuring_bind,
  "si::quasiquote": le__sf_quasiquote,
  }
}

///|
let le__special_table : Ref[Map[String, LeSpecialHandler]?] = Ref(None)

///|
fn le__special_forms() -> Map[String, LeSpecialHandler] {
  match le__special_table.val {
    Some(m) => m
    None => {
      let m = le__make_special_table()
      le__special_table.val = Some(m)
      m
    }
  }
}

///|
fn le__sf_quote(args : Value, _form : Value, _env : LeEnv, mv : Bool) -> LeCode raise {
  le__single(le__const(car(args)), mv)
}

///|
fn le__sf_function(args : Value, form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let x = car(args)
  let c : LeCode = match x {
    Sym(s) =>
      match le__lookup_fun(env, s) {
        LexFun(d, i) => f => le__frame_at(f, d).vals[i]
        _ =>
          _f => match s.func {
            Some(lf) => Func(lf)
            None => le__undefined_function(x)
          }
      }
    Cons({ car: Sym({ name: "lambda", .. }), .. }) => le__comp_function(x, env)
    Cons({ car: Sym({ name: "setf", .. }), cdr: Cons({ car: Sym(s), .. }) }) =>
      _f => match le__setf_functions.get(s.name) {
        Some(fv) => fv
        None => le__undefined_function(x)
      }
    _ => {
      le__error("function: invalid function name " + prin1_to_string(form))
      |> ignore
      le__const(Nil)
    }
  }
  le__single(c, mv)
}

///|
fn le__sf_setq(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let codes : Array[LeCode] = []
  let mut l = args
  while l is Cons({ car: v, cdr: Cons({ car: x, cdr: rest }) }) {
    match v {
      Sym(s) => codes.push(le__comp_setvar(s, env, le__comp(x, env, false)))
      _ => le__error("setq: not a variable: " + prin1_to_string(v)) |> ignore
    }
    l = rest
  }
  if l is Cons(_) {
    le__error("setq: odd number of arguments") |> ignore
  }
  let c : LeCode = match codes.length() {
    0 => le__const(Nil)
    1 => codes[0]
    n =>
      f => {
        for i in 0..<(n - 1) {
          (codes[i])(f) |> ignore
        }
        (codes[n - 1])(f)
      }
  }
  le__single(c, mv)
}

///|
fn le__sf_if(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let tc = le__comp(car(args), env, false)
  let a = le__comp(cadr(args), env, mv)
  let b = le__comp(caddr(args), env, mv)
  f => if tc(f) is Nil { b(f) } else { a(f) }
}

///|
fn le__sf_progn(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  le__comp_progn(args, env, mv)
}

///|
fn le__binding_parts(b : Value) -> (Value, Value) {
  match b {
    Cons({ car: v, cdr: rest }) => (v, car(rest))
    _ => (b, Nil)
  }
}

///|
fn le__binding_sym(v : Value) -> Symbol raise {
  match v {
    Sym(s) => s
    _ => {
      le__program_error("invalid variable in binding: " + prin1_to_string(v))
      |> ignore
      intern("nil")
    }
  }
}

///|
fn le__sf_let(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let bindings = car(args)
  let (specials, body) = le__parse_body(cdr(args), false)
  let syms : Array[Symbol] = []
  let inits : Array[LeCode?] = []
  for b in bindings.iter() {
    let (v, init) = le__binding_parts(b)
    syms.push(le__binding_sym(v))
    inits.push(if init is Nil { None } else { Some(le__comp(init, env, false)) })
  }
  let any_lex = syms.iter().any(s => !(le__sym_in(s, specials) || le__special_p(s)))
  let finfo = { size: 0 }
  let mut e = if any_lex { Frame(finfo, env) } else { env }
  let params : Array[LeParam] = []
  for s in syms {
    if le__sym_in(s, specials) || le__special_p(s) {
      e = Special(s, e)
      params.push(PDyn(Sym(s)))
    } else {
      let slot = finfo.size
      finfo.size += 1
      e = Var(s, slot, e)
      params.push(PLex(slot))
    }
  }
  let benv = le__add_free_specials(e, specials, syms)
  let bc = le__comp_progn(body, benv, mv)
  let n = syms.length()
  let any_dyn = params.iter().any(p => p is PDyn(_))
  if n == 0 {
    return bc
  }
  f => {
    let vals = Array::make(n, Value::Nil)
    for i in 0..<n {
      match inits[i] {
        Some(c) => vals[i] = c(f)
        None => ()
      }
    }
    let fr = if any_lex { le__new_frame(finfo, f) } else { f }
    if any_dyn {
      let binds : Array[Binding] = []
      defer {
        for k = binds.length() - 1; k >= 0; k = k - 1 {
          unbind(binds[k])
        }
      }
      for i in 0..<n {
        le__bind_param(params[i], vals[i], fr, binds)
      }
      bc(fr)
    } else {
      for i in 0..<n {
        match params[i] {
          PLex(slot) => fr.vals[slot] = vals[i]
          _ => ()
        }
      }
      bc(fr)
    }
  }
}

///|
fn le__sf_let_star(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let bindings = car(args)
  let (specials, body) = le__parse_body(cdr(args), false)
  let pairs : Array[(Symbol, Value)] = []
  for b in bindings.iter() {
    let (v, init) = le__binding_parts(b)
    pairs.push((le__binding_sym(v), init))
  }
  let syms = pairs.map(p => p.0)
  let any_lex = syms.iter().any(s => !(le__sym_in(s, specials) || le__special_p(s)))
  let finfo = { size: 0 }
  let mut e = if any_lex { Frame(finfo, env) } else { env }
  let steps : Array[(LeParam, LeCode?)] = []
  for p in pairs {
    let (s, init) = p
    let ic = if init is Nil { None } else { Some(le__comp(init, e, false)) }
    if le__sym_in(s, specials) || le__special_p(s) {
      e = Special(s, e)
      steps.push((PDyn(Sym(s)), ic))
    } else {
      let slot = finfo.size
      finfo.size += 1
      e = Var(s, slot, e)
      steps.push((PLex(slot), ic))
    }
  }
  let benv = le__add_free_specials(e, specials, syms)
  let bc = le__comp_progn(body, benv, mv)
  if steps.length() == 0 {
    return bc
  }
  let any_dyn = steps.iter().any(p => p.0 is PDyn(_))
  f => {
    let fr = if any_lex { le__new_frame(finfo, f) } else { f }
    let binds : Array[Binding] = []
    defer {
      if any_dyn {
        for k = binds.length() - 1; k >= 0; k = k - 1 {
          unbind(binds[k])
        }
      }
    }
    for st in steps {
      let v = match st.1 {
        Some(c) => c(fr)
        None => Nil
      }
      le__bind_param(st.0, v, fr, binds)
    }
    bc(fr)
  }
}

///|
fn le__fname_sym(v : Value) -> Symbol raise {
  match v {
    Sym(s) => s
    _ => {
      le__program_error("invalid function name: " + prin1_to_string(v))
      |> ignore
      intern("nil")
    }
  }
}

///|
fn le__sf_flet(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  le__comp_flet(args, env, mv, false)
}

///|
fn le__sf_labels(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  le__comp_flet(args, env, mv, true)
}

///|
fn le__comp_flet(args : Value, env : LeEnv, mv : Bool, rec : Bool) -> LeCode raise {
  let defs = list_to_array(car(args))
  let (specials, body) = le__parse_body(cdr(args), false)
  let finfo = { size: 0 }
  let mut e = Frame(finfo, env)
  let slots = []
  for d in defs {
    let s = le__fname_sym(car(d))
    let slot = finfo.size
    finfo.size += 1
    e = Fun(s, slot, e)
    slots.push(slot)
  }
  // flet functions see the outer environment, labels the new one
  let lenv = if rec { e } else { env }
  let lams = defs.map(d => le__new_lambda(
    symbol_name(car(d)) catch { _ => "flet" },
    cadr(d),
    cddr(d),
    lenv,
    Some(car(d)),
  ))
  let benv = le__add_free_specials(e, specials, [])
  let bc = le__comp_progn(body, benv, mv)
  f => {
    let fr = le__new_frame(finfo, f)
    for i, lam in lams {
      fr.vals[slots[i]] = le__make_closure(lam, Some(if rec { fr } else { f }))
    }
    bc(fr)
  }
}

///|
fn le__sf_macrolet(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let mut e = env
  for d in car(args).iter() {
    let s = le__fname_sym(car(d))
    let expander = le__make_macro_expander(car(d), cadr(d), cddr(d), Top, None)
    e = Mac(s, expander, e)
  }
  let (specials, body) = le__parse_body(cdr(args), false)
  le__comp_progn(body, le__add_free_specials(e, specials, []), mv)
}

///|
fn le__sf_symbol_macrolet(
  args : Value,
  _form : Value,
  env : LeEnv,
  mv : Bool,
) -> LeCode raise {
  let mut e = env
  for d in car(args).iter() {
    e = SymMacro(le__binding_sym(car(d)), cadr(d), e)
  }
  let (specials, body) = le__parse_body(cdr(args), false)
  le__comp_progn(body, le__add_free_specials(e, specials, []), mv)
}

///|
fn le__comp_block(name : Value, body : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let slot = le__alloc_slot(env)
  let info = { used: false, mv }
  let bc = le__comp_progn(body, Block(name, slot, info, env), mv)
  if !info.used {
    return bc
  }
  f => {
    let tag = cons(Nil, Nil)
    f.vals[slot] = tag
    bc(f) catch {
      LispError::ReturnFrom(tg, v) if physical_equal_value(tg, tag) => v
      e => raise e
    }
  }
}

///|
fn le__sf_block(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  le__comp_block(car(args), cdr(args), env, mv)
}

///|
fn le__sf_return_from(args : Value, _form : Value, env : LeEnv, _mv : Bool) -> LeCode raise {
  let name = car(args)
  let mut e = env
  let mut depth = 0
  while true {
    match e {
      Top => break
      Frame(_, p) => {
        depth += 1
        e = p
      }
      Block(n, slot, info, p) => {
        if eq(n, name) {
          info.used = true
          let vc = le__comp(cadr(args), env, info.mv)
          let d = depth
          return f => {
            let v = vc(f)
            raise LispError::ReturnFrom(le__frame_at(f, d).vals[slot], v)
          }
        }
        e = p
      }
      Var(_, _, p) | Special(_, p) | SymMacro(_, _, p) | Fun(_, _, p) | Mac(_, _, p) =>
        e = p
      Tags(_, _, _, _, p) => e = p
    }
  }
  le__error("return-from: unknown block " + prin1_to_string(name)) |> ignore
  le__const(Nil)
}

///|
fn le__tag_p(x : Value) -> Bool {
  x is (Sym(_) | Fix(_) | Big(_) | Nil)
}

///|
fn le__sf_tagbody(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let tags : Array[Value] = []
  let idxs : Array[Int] = []
  let stmts : Array[Value] = []
  for x in args.iter() {
    if le__tag_p(x) {
      tags.push(x)
      idxs.push(stmts.length())
    } else {
      stmts.push(x)
    }
  }
  if tags.length() == 0 {
    let codes = stmts.map(x => le__comp(x, env, false))
    return le__single(
      f => {
        for c in codes {
          c(f) |> ignore
        }
        Nil
      },
      mv,
    )
  }
  let slot = le__alloc_slot(env)
  let info = { used: false, mv: false }
  let e = Tags(tags, idxs, slot, info, env)
  let codes : Array[LeCode] = []
  for x in stmts {
    codes.push(le__comp(x, e, false))
  }
  let n = codes.length()
  if !info.used {
    return le__single(
      f => {
        for c in codes {
          c(f) |> ignore
        }
        Nil
      },
      mv,
    )
  }
  le__single(
    f => {
      let tok = cons(Nil, Nil)
      f.vals[slot] = tok
      let mut pc = 0
      while pc < n {
        let c = codes[pc]
        pc = try {
          c(f) |> ignore
          pc + 1
        } catch {
          LispError::Go(Cons({ car: tg, cdr: Fix(k) })) if physical_equal_value(
              tg, tok,
            ) => k.to_int()
          e => raise e
        }
      }
      Nil
    },
    mv,
  )
}

///|
fn le__sf_go(args : Value, _form : Value, env : LeEnv, _mv : Bool) -> LeCode raise {
  let tag = car(args)
  let mut e = env
  let mut depth = 0
  while true {
    match e {
      Top => break
      Frame(_, p) => {
        depth += 1
        e = p
      }
      Tags(tags, idxs, slot, info, p) => {
        for i, tg in tags {
          if eql(tg, tag) {
            info.used = true
            let d = depth
            let target = Value::Fix(idxs[i].to_int64())
            return f => raise LispError::Go(
                cons(le__frame_at(f, d).vals[slot], target),
              )
          }
        }
        e = p
      }
      Var(_, _, p) | Special(_, p) | SymMacro(_, _, p) | Fun(_, _, p) | Mac(_, _, p) =>
        e = p
      Block(_, _, _, p) => e = p
    }
  }
  le__error("go: no tag named " + prin1_to_string(tag) + " is visible")
  |> ignore
  le__const(Nil)
}

///|
fn le__sf_catch(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let tc = le__comp(car(args), env, false)
  let bc = le__comp_progn(cdr(args), env, mv)
  f => {
    let tg = tc(f)
    bc(f) catch {
      LispError::Throw(x, v) if eq(x, tg) => v
      e => raise e
    }
  }
}

///|
fn le__sf_throw(args : Value, _form : Value, env : LeEnv, _mv : Bool) -> LeCode raise {
  let tc = le__comp(car(args), env, false)
  let vc = le__comp(cadr(args), env, true)
  f => {
    let tg = tc(f)
    let v = vc(f)
    raise LispError::Throw(tg, v)
  }
}

///|
fn le__sf_unwind_protect(
  args : Value,
  _form : Value,
  env : LeEnv,
  mv : Bool,
) -> LeCode raise {
  let pc = le__comp(car(args), env, mv)
  let cc = le__comp_progn(cdr(args), env, false)
  f => {
    let r = pc(f) catch {
      e => {
        let saved = le__mv.val
        cc(f) |> ignore
        le__mv.val = saved
        raise e
      }
    }
    let saved = le__mv.val
    cc(f) |> ignore
    le__mv.val = saved
    r
  }
}

///|
fn le__sf_eval_when(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  if le__eval_when_executes(car(args), false) {
    le__comp_progn(cdr(args), env, mv)
  } else {
    le__single(le__const(Nil), mv)
  }
}

///|
fn le__sf_locally(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let (specials, body) = le__parse_body(args, false)
  le__comp_progn(body, le__add_free_specials(env, specials, []), mv)
}

///|
fn le__sf_the(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  le__comp(cadr(args), env, mv)
}

///|
fn le__sf_mv_call(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let fc = le__comp(car(args), env, false)
  let codes = list_to_array(cdr(args)).map(x => le__comp(x, env, true))
  ignore(mv)
  f => {
    let fv = fc(f)
    let all : Array[Value] = []
    for c in codes {
      le__mv.val = None
      let v = c(f)
      for x in le__values_of(v) {
        all.push(x)
      }
    }
    le__mv.val = None
    le__funcall(fv, all)
  }
}

///|
fn le__sf_mv_prog1(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let c1 = le__comp(car(args), env, mv)
  let rest = le__comp_progn(cdr(args), env, false)
  f => {
    let v = c1(f)
    let saved = le__mv.val
    rest(f) |> ignore
    le__mv.val = saved
    v
  }
}

///|
fn le__sf_mv_bind(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let vars = list_to_array(car(args)).map(v => le__binding_sym(v))
  let vc = le__comp(cadr(args), env, true)
  let (specials, body) = le__parse_body(cddr(args), false)
  let finfo = { size: 0 }
  let mut e = Frame(finfo, env)
  let params : Array[LeParam] = []
  for s in vars {
    if le__sym_in(s, specials) || le__special_p(s) {
      e = Special(s, e)
      params.push(PDyn(Sym(s)))
    } else {
      let slot = finfo.size
      finfo.size += 1
      e = Var(s, slot, e)
      params.push(PLex(slot))
    }
  }
  let bc = le__comp_progn(body, le__add_free_specials(e, specials, vars), mv)
  f => {
    le__mv.val = None
    let vals = le__values_of(vc(f))
    let fr = le__new_frame(finfo, f)
    let binds : Array[Binding] = []
    defer {
      for k = binds.length() - 1; k >= 0; k = k - 1 {
        unbind(binds[k])
      }
    }
    for i, p in params {
      le__bind_param(p, if i < vals.length() { vals[i] } else { Nil }, fr, binds)
    }
    bc(fr)
  }
}

///|
fn le__sf_progv(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let sc = le__comp(car(args), env, false)
  let vc = le__comp(cadr(args), env, false)
  let bc = le__comp_progn(cddr(args), env, mv)
  f => {
    let syms = sc(f)
    let vals = vc(f)
    progv(syms, vals, () => bc(f))
  }
}

///|
fn le__sf_load_time_value(
  args : Value,
  _form : Value,
  _env : LeEnv,
  mv : Bool,
) -> LeCode raise {
  let form = car(args)
  let cell : Ref[Value?] = Ref(None)
  le__single(
    _f => match cell.val {
      Some(v) => v
      None => {
        let v = le__eval_toplevel(form)
        cell.val = Some(v)
        v
      }
    },
    mv,
  )
}

///|
fn le__sf_declare(_args : Value, form : Value, _env : LeEnv, _mv : Bool) -> LeCode raise {
  // a declaration where a form is evaluated (as SBCL reports it)
  let msg = "There is no function named DECLARE.  References to DECLARE in some contexts (like starts of blocks) are unevaluated expressions, but here the expression is being evaluated, which invokes undefined behaviour: " +
    prin1_to_string(form)
  _f => raise LispError::Condition(intern("undefined-function"), msg, sym("declare"))
}

///|
/// Functions defined with DEFUN (SETF name), by name.
let le__setf_functions : Map[String, Value] = Map::new()

///|
/// Install a function in a symbol's function cell (as DEFUN does).
fn le__install_function(name : Value, fv : Value) -> Unit raise {
  match (name, fv) {
    (Sym(s), Func(lf)) => {
      s.func = Some(lf)
      remprop(name, le__q_macro_function) |> ignore
    }
    (Cons({ car: Sym({ name: "setf", .. }), cdr: Cons({ car: Sym(s), .. }) }), _) =>
      le__setf_functions[s.name] = fv
    _ => le__error("defun: invalid function name " + prin1_to_string(name)) |> ignore
  }
}

///|
fn le__sf_defun(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let name = car(args)
  let mut ll = cadr(args)
  let body = cddr(args)
  match ll {
    Sym({ name: "macro", .. }) => {
      // Maclisp (defun name macro (form) body): a macro of the whole form
      let fll = car(body)
      return le__sf_defmacro(
        list_star([
          name,
          list4(le__q_amp_whole, car(fll), le__q_amp_rest, gensym(prefix="ignore")),
          cdr(body),
        ]),
        Nil,
        env,
        mv,
      )
    }
    Sym(_) =>
      // Maclisp lexpr (defun name n body): N is the argument count
      ll = list([
        le__q_amp_rest,
        sym("narg-rest-argument"),
        le__q_amp_aux,
        list2(ll, list2(sym("length"), sym("narg-rest-argument"))),
      ])
    _ => ()
  }
  let block_name = match name {
    Cons({ car: _, cdr: Cons({ car: n, .. }) }) => n
    _ => name
  }
  let pname = match name {
    Sym(s) => s.name
    _ => prin1_to_string(name)
  }
  let lam = le__new_lambda(pname, ll, body, env, Some(block_name))
  le__single(
    f => {
      le__install_function(name, le__make_closure(lam, Some(f)))
      name
    },
    mv,
  )
}

///|
fn le__sf_defmacro(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  let name = car(args)
  let ll = cadr(args)
  let body = cddr(args)
  le__single(
    f => {
      let expander = le__make_macro_expander(name, ll, body, env, Some(f))
      match name {
        Sym(s) => s.func = None
        _ => ()
      }
      putprop(name, expander, le__q_macro_function) |> ignore
      name
    },
    mv,
  )
}

///|
fn le__sf_destructuring_bind(
  args : Value,
  _form : Value,
  env : LeEnv,
  mv : Bool,
) -> LeCode raise {
  let ll = car(args)
  let vc = le__comp(cadr(args), env, false)
  let (specials, body) = le__parse_body(cddr(args), false)
  let finfo = { size: 0 }
  let st = {
    env: Frame(finfo, env),
    finfo,
    specials,
    bound: [],
    any_dyn: false,
  }
  let pat = st.dlist(ll)
  let bc = le__comp_progn(
    body,
    le__add_free_specials(st.env, specials, st.bound),
    mv,
  )
  f => {
    let v = vc(f)
    let fr = le__new_frame(finfo, f)
    let binds : Array[Binding] = []
    defer {
      for k = binds.length() - 1; k >= 0; k = k - 1 {
        unbind(binds[k])
      }
    }
    le__dbind_list(pat, v, fr, binds, "destructuring-bind")
    bc(fr)
  }
}

///|
fn le__sf_quasiquote(args : Value, _form : Value, env : LeEnv, mv : Bool) -> LeCode raise {
  le__comp(le__qq_expand(car(args), 1).0, env, mv)
}

// ---------------------------------------------------------------------------
// Backquote

///|
fn le__qq_quote(x : Value) -> Value {
  match x {
    Nil | Fix(_) | Big(_) | Flo(_) | Str(_) | Char(_) | Ratio(_, _) => x
    Sym(s) if s.name == "t" || s.name.has_prefix(":") => x
    _ => list2(sym("quote"), x)
  }
}

///|
fn le__qq_form_p(x : Value, head : Value) -> Bool {
  match x {
    Cons({ car: h, cdr: Cons({ car: _, cdr: Nil }) }) => eq(h, head)
    _ => false
  }
}

///|
/// Expand a backquoted template at nesting `depth`; returns the form and
/// whether it is constant (then the form is a quoted constant).
fn le__qq_expand(x : Value, depth : Int) -> (Value, Bool) {
  if le__qq_form_p(x, @lisp.q_unquote) {
    if depth == 1 {
      return (cadr(x), false)
    }
    let (inner, c) = le__qq_expand(cadr(x), depth - 1)
    if c {
      return (le__qq_quote(x), true)
    }
    return (list3(sym("list"), list2(sym("quote"), @lisp.q_unquote), inner), false)
  }
  if le__qq_form_p(x, @lisp.q_unquote_splicing) && depth > 1 {
    let (inner, c) = le__qq_expand(cadr(x), depth - 1)
    if c {
      return (le__qq_quote(x), true)
    }
    return (
      list3(sym("list"), list2(sym("quote"), @lisp.q_unquote_splicing), inner),
      false,
    )
  }
  if le__qq_form_p(x, @lisp.q_quasiquote) {
    let (inner, c) = le__qq_expand(cadr(x), depth + 1)
    if c {
      return (le__qq_quote(x), true)
    }
    return (list3(sym("list"), list2(sym("quote"), @lisp.q_quasiquote), inner), false)
  }
  match x {
    Cons(_) => {
      // segments of an APPEND
      let segs : Array[Value] = []
      let cur : Array[Value] = []
      let mut all_const = true
      let mut l = x
      let mut tail : Value = Nil
      let mut tail_const = true
      while true {
        match l {
          Nil => break
          Cons({ car: e, cdr: rest }) => {
            if le__qq_form_p(l, @lisp.q_unquote) || le__qq_form_p(l, @lisp.q_quasiquote) {
              // dotted unquote: `(a . ,b)
              let (tf, tc) = le__qq_expand(l, depth)
              tail = tf
              tail_const = tc
              break
            }
            if le__qq_form_p(e, @lisp.q_unquote_splicing) && depth == 1 {
              if cur.length() > 0 {
                segs.push(cons(sym("list"), list(cur)))
                cur.clear()
              }
              segs.push(cadr(e))
              all_const = false
            } else {
              let (ef, ec) = le__qq_expand(e, depth)
              if !ec {
                all_const = false
              }
              cur.push(ef)
            }
            l = rest
          }
          _ => {
            tail = le__qq_quote(l)
            break
          }
        }
      }
      if all_const && tail_const {
        return (le__qq_quote(x), true)
      }
      if cur.length() > 0 {
        segs.push(cons(sym("list"), list(cur)))
      }
      if !(tail is Nil) {
        segs.push(tail)
      }
      if segs.length() == 1 && (cur.length() > 0 || tail is Nil) {
        // a single LIST segment or a single splice (must copy? CL allows
        // sharing of the last splice)
        return (segs[0], false)
      }
      (cons(sym("append"), list(segs)), false)
    }
    Vec(_) => {
      let l = vector_to_list(x) catch { _ => Nil }
      let (lf, c) = le__qq_expand(l, depth)
      if c {
        return (le__qq_quote(x), true)
      }
      (list3(sym("apply"), list2(sym("function"), sym("vector")), lf), false)
    }
    _ => (le__qq_quote(x), true)
  }
}
