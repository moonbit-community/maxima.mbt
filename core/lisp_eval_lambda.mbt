// Lisp evaluator: lambda lists, closures, destructuring.

///|
priv enum LeParam {
  PLex(Int)
  PDyn(Value)
}

///|
priv struct LeOptP {
  p : LeParam
  init : LeCode?
  sp : LeParam?
}

///|
priv struct LeKeyP {
  kw : Value
  p : LeParam
  init : LeCode?
  sp : LeParam?
}

///|
priv struct LeCompiled {
  req : Array[LeParam]
  opt : Array[LeOptP]
  rest : LeParam?
  has_key : Bool
  keys : Array[LeKeyP]
  allow_other : Bool
  aux : Array[(LeParam, LeCode?)]
  finfo : LeFInfo
  any_dyn : Bool
  body : LeCode
}

///|
/// A lambda expression together with its compile-time environment; shared
/// by all closures made from it, compiled on first call.
priv struct LeLambda {
  name : String
  ll : Value
  body : Value
  env : LeEnv
  block : Value?
  mut compiled : LeCompiled?
}

///|
/// Builder state while compiling a lambda list: the environment grows
/// parameter by parameter (default forms see the earlier parameters).
priv struct LeLLState {
  mut env : LeEnv
  finfo : LeFInfo
  specials : Array[Symbol]
  bound : Array[Symbol]
  mut any_dyn : Bool
}

///|
fn LeLLState::param(self : LeLLState, v : Value) -> LeParam raise {
  let s = match v {
    Sym(s) => s
    _ => {
      le__program_error("invalid lambda variable: " + prin1_to_string(v))
      |> ignore
      intern("nil")
    }
  }
  self.bound.push(s)
  if le__sym_in(s, self.specials) || le__special_p(s) {
    self.env = Special(s, self.env)
    self.any_dyn = true
    PDyn(v)
  } else {
    let slot = self.finfo.size
    self.finfo.size += 1
    self.env = Var(s, slot, self.env)
    PLex(slot)
  }
}

///|
fn LeLLState::init(self : LeLLState, form : Value) -> LeCode? raise {
  if form is Nil {
    None
  } else {
    Some(le__comp(form, self.env, false))
  }
}

///|
fn le__kw_of(v : Value) -> Value raise {
  match v {
    Sym(s) =>
      if s.name.has_prefix(":") {
        v
      } else {
        sym(":" + s.name)
      }
    _ => le__program_error("invalid &key variable: " + prin1_to_string(v))
  }
}

///|
fn le__is_amp(v : Value) -> Bool {
  match v {
    Sym(s) => s.name.has_prefix("&")
    _ => false
  }
}

///|
fn le__compile_lambda(lam : LeLambda) -> LeCompiled raise {
  let (specials, body) = le__parse_body(lam.body, true)
  let finfo = { size: 0 }
  let st = {
    env: Frame(finfo, lam.env),
    finfo,
    specials,
    bound: [],
    any_dyn: false,
  }
  let req = []
  let opt = []
  let mut rest = None
  let mut has_key = false
  let keys = []
  let mut allow_other = false
  let aux = []
  let mut mode = 0 // 0 req, 1 opt, 2 rest, 3 key, 4 aux
  let mut l = lam.ll
  while true {
    match l {
      Nil => break
      Sym(_) => {
        // dotted rest parameter
        rest = Some(st.param(l))
        break
      }
      Cons({ car: x, cdr: next }) => {
        l = next
        if eq(x, le__q_amp_optional) {
          mode = 1
        } else if eq(x, le__q_amp_rest) || eq(x, le__q_amp_body) {
          mode = 2
        } else if eq(x, le__q_amp_key) {
          mode = 3
          has_key = true
        } else if eq(x, le__q_amp_allow) {
          allow_other = true
        } else if eq(x, le__q_amp_aux) {
          mode = 4
        } else if le__is_amp(x) {
          le__program_error(
            "unsupported lambda-list keyword " + prin1_to_string(x),
          )
          |> ignore
        } else {
          match mode {
            0 => req.push(st.param(x))
            1 =>
              match x {
                Cons({ car: v, cdr: more }) => {
                  let init = st.init(car(more))
                  let p = st.param(v)
                  let sp = if cdr(more) is Cons(_) {
                    Some(st.param(cadr(more)))
                  } else {
                    None
                  }
                  opt.push({ p, init, sp })
                }
                _ => opt.push({ p: st.param(x), init: None, sp: None })
              }
            2 => rest = Some(st.param(x))
            3 =>
              match x {
                Cons({ car: spec, cdr: more }) => {
                  let (kw, v) = match spec {
                    Cons({ car: k, cdr: Cons({ car: v, .. }) }) => (k, v)
                    _ => (le__kw_of(spec), spec)
                  }
                  let init = st.init(car(more))
                  let p = st.param(v)
                  let sp = if cdr(more) is Cons(_) {
                    Some(st.param(cadr(more)))
                  } else {
                    None
                  }
                  keys.push({ kw, p, init, sp })
                }
                _ => keys.push({ kw: le__kw_of(x), p: st.param(x), init: None, sp: None })
              }
            _ =>
              match x {
                Cons({ car: v, cdr: more }) => {
                  let init = st.init(car(more))
                  aux.push((st.param(v), init))
                }
                _ => aux.push((st.param(x), None))
              }
          }
        }
      }
      _ => break
    }
  }
  let benv = le__add_free_specials(st.env, specials, st.bound)
  let bc = match lam.block {
    Some(name) => le__comp_block(name, body, benv, true)
    None => le__comp_progn(body, benv, true)
  }
  {
    req,
    opt,
    rest,
    has_key,
    keys,
    allow_other,
    aux,
    finfo,
    any_dyn: st.any_dyn,
    body: bc,
  }
}

///|
fn le__bind_param(
  p : LeParam,
  v : Value,
  fr : LeFrame,
  binds : Array[Binding],
) -> Unit {
  match p {
    PLex(i) => fr.vals[i] = v
    PDyn(s) => binds.push(bind(s, v))
  }
}

///|
fn le__arg_count_error(name : String, n : Int) -> Value raise {
  le__program_error(
    "invalid number of arguments: \{n}" +
    (if name == "" { "" } else { " (in a call to " + name + ")" }),
  )
}

///|
fn le__invoke(lam : LeLambda, captured : LeFrame?, args : Array[Value]) -> Value raise {
  let c = match lam.compiled {
    Some(c) => c
    None => {
      let c = le__compile_lambda(lam)
      lam.compiled = Some(c)
      c
    }
  }
  let fr = { vals: Array::make(c.finfo.size, Value::Nil), up: captured }
  let n = args.length()
  let nreq = c.req.length()
  if n < nreq {
    return le__arg_count_error(lam.name, n)
  }
  let binds : Array[Binding] = []
  defer {
    if binds.length() > 0 {
      for k = binds.length() - 1; k >= 0; k = k - 1 {
        unbind(binds[k])
      }
    }
  }
  for i in 0..<nreq {
    le__bind_param(c.req[i], args[i], fr, binds)
  }
  let mut i = nreq
  for o in c.opt {
    if i < n {
      le__bind_param(o.p, args[i], fr, binds)
      i += 1
      match o.sp {
        Some(sp) => le__bind_param(sp, t, fr, binds)
        None => ()
      }
    } else {
      let v = match o.init {
        Some(ic) => ic(fr)
        None => Nil
      }
      le__bind_param(o.p, v, fr, binds)
      match o.sp {
        Some(sp) => le__bind_param(sp, Nil, fr, binds)
        None => ()
      }
    }
  }
  match c.rest {
    Some(r) => le__bind_param(r, list_view(args[i:]), fr, binds)
    None => ()
  }
  if c.has_key {
    if (n - i) % 2 != 0 {
      return le__program_error(
        "odd number of &key arguments" +
        (if lam.name == "" { "" } else { " in a call to " + lam.name }),
      )
    }
    let mut allow = c.allow_other
    // :allow-other-keys t in the call
    let mut j = i
    while j + 1 < n {
      if args[j] is Sym({ name: ":allow-other-keys", .. }) &&
        args[j + 1].truthy() {
        allow = true
      }
      j += 2
    }
    if !allow {
      let mut j = i
      while j + 1 < n {
        let k = args[j]
        let mut known = k is Sym({ name: ":allow-other-keys", .. })
        for kp in c.keys {
          if eq(kp.kw, k) {
            known = true
          }
        }
        if !known {
          return le__program_error(
            "unknown &key argument: " +
            prin1_to_string(k) +
            (if lam.name == "" { "" } else { " in a call to " + lam.name }),
          )
        }
        j += 2
      }
    }
    for kp in c.keys {
      let mut found : Value? = None
      let mut j = i
      while j + 1 < n {
        if eq(args[j], kp.kw) {
          found = Some(args[j + 1])
          break
        }
        j += 2
      }
      match found {
        Some(v) => {
          le__bind_param(kp.p, v, fr, binds)
          match kp.sp {
            Some(sp) => le__bind_param(sp, t, fr, binds)
            None => ()
          }
        }
        None => {
          let v = match kp.init {
            Some(ic) => ic(fr)
            None => Nil
          }
          le__bind_param(kp.p, v, fr, binds)
          match kp.sp {
            Some(sp) => le__bind_param(sp, Nil, fr, binds)
            None => ()
          }
        }
      }
    }
  } else if c.rest is None && i < n {
    return le__arg_count_error(lam.name, n)
  }
  for a in c.aux {
    let v = match a.1 {
      Some(ic) => ic(fr)
      None => Nil
    }
    le__bind_param(a.0, v, fr, binds)
  }
  (c.body)(fr)
}

///|
fn le__make_closure(lam : LeLambda, fr : LeFrame?) -> Value {
  Func({ name: lam.name, call: args => le__invoke(lam, fr, args) })
}

///|
fn le__new_lambda(
  name : String,
  ll : Value,
  body : Value,
  env : LeEnv,
  block : Value?,
) -> LeLambda raise {
  let lam : LeLambda = { name, ll, body, env, block, compiled: None }
  // The body is compiled on the first call, except when it may refer to an
  // enclosing BLOCK or TAGBODY: those must know at their own compilation
  // whether a RETURN-FROM or GO reaches them.
  if le__env_has_exits(env) {
    lam.compiled = Some(le__compile_lambda(lam))
  }
  lam
}

///|
fn le__env_has_exits(env : LeEnv) -> Bool {
  let mut e = env
  while true {
    match e {
      Top => return false
      Block(_, _, _, _) | Tags(_, _, _, _, _) => return true
      Frame(_, p) | Var(_, _, p) | Special(_, p) | SymMacro(_, _, p) | Fun(_, _, p) =>
        e = p
      Mac(_, _, p) => e = p
    }
  }
  false
}

///|
/// Code creating a closure for a (lambda ll . body) form.
fn le__comp_function(lform : Value, env : LeEnv) -> LeCode raise {
  match lform {
    Cons({ car: _, cdr: Cons({ car: ll, cdr: body }) }) => {
      let lam = le__new_lambda("lambda", ll, body, env, None)
      f => le__make_closure(lam, Some(f))
    }
    _ => {
      le__program_error("malformed lambda expression: " + prin1_to_string(lform))
      |> ignore
      le__const(Nil)
    }
  }
}

///|
/// A closure for a lambda expression given as data (null environment).
fn le__closure_of_lambda(
  lform : Value,
  env : LeEnv,
  fr : LeFrame?,
) -> Value raise {
  match lform {
    Cons({ car: _, cdr: Cons({ car: ll, cdr: body }) }) =>
      le__make_closure(le__new_lambda("lambda", ll, body, env, None), fr)
    _ => le__program_error("malformed lambda expression: " + prin1_to_string(lform))
  }
}

// ---------------------------------------------------------------------------
// Destructuring lambda lists (DEFMACRO, DESTRUCTURING-BIND)

///|
priv enum LeDest {
  DVar(LeParam)
  DList(LeDList)
}

///|
priv struct LeDList {
  whole : LeDest?
  req : Array[LeDest]
  opt : Array[(LeDest, LeCode?, LeParam?)]
  rest : LeDest?
  has_key : Bool
  keys : Array[(Value, LeDest, LeCode?, LeParam?)]
  allow_other : Bool
  aux : Array[(LeDest, LeCode?)]
  env_var : LeParam?
}

///|
fn LeLLState::dest(self : LeLLState, pat : Value) -> LeDest raise {
  match pat {
    Cons(_) => DList(self.dlist(pat))
    _ => DVar(self.param(pat))
  }
}

///|
fn LeLLState::dlist(self : LeLLState, pat : Value) -> LeDList raise {
  let mut whole = None
  let req = []
  let opt = []
  let mut rest = None
  let mut has_key = false
  let keys = []
  let mut allow_other = false
  let aux = []
  let mut env_var = None
  let mut mode = 0
  let mut l = pat
  while true {
    match l {
      Nil => break
      Sym(_) => {
        rest = Some(DVar(self.param(l)))
        break
      }
      Cons({ car: x, cdr: next }) => {
        l = next
        if eq(x, le__q_amp_whole) {
          whole = Some(self.dest(car(l)))
          l = cdr(l)
        } else if eq(x, le__q_amp_env) {
          env_var = Some(self.param(car(l)))
          l = cdr(l)
        } else if eq(x, le__q_amp_optional) {
          mode = 1
        } else if eq(x, le__q_amp_rest) || eq(x, le__q_amp_body) {
          mode = 2
        } else if eq(x, le__q_amp_key) {
          mode = 3
          has_key = true
        } else if eq(x, le__q_amp_allow) {
          allow_other = true
        } else if eq(x, le__q_amp_aux) {
          mode = 4
        } else {
          match mode {
            0 => req.push(self.dest(x))
            1 =>
              match x {
                Cons({ car: v, cdr: more }) => {
                  let init = self.init(car(more))
                  let d = self.dest(v)
                  let sp = if cdr(more) is Cons(_) {
                    Some(self.param(cadr(more)))
                  } else {
                    None
                  }
                  opt.push((d, init, sp))
                }
                _ => opt.push((self.dest(x), None, None))
              }
            2 => rest = Some(self.dest(x))
            3 =>
              match x {
                Cons({ car: spec, cdr: more }) => {
                  let (kw, v) = match spec {
                    Cons({ car: k, cdr: Cons({ car: v, .. }) }) => (k, v)
                    _ => (le__kw_of(spec), spec)
                  }
                  let init = self.init(car(more))
                  let d = self.dest(v)
                  let sp = if cdr(more) is Cons(_) {
                    Some(self.param(cadr(more)))
                  } else {
                    None
                  }
                  keys.push((kw, d, init, sp))
                }
                _ => keys.push((le__kw_of(x), self.dest(x), None, None))
              }
            _ =>
              match x {
                Cons({ car: v, cdr: more }) => {
                  let init = self.init(car(more))
                  aux.push((self.dest(v), init))
                }
                _ => aux.push((self.dest(x), None))
              }
          }
        }
      }
      _ => break
    }
  }
  { whole, req, opt, rest, has_key, keys, allow_other, aux, env_var }
}

///|
fn le__destructure_error(what : String, v : Value) -> Value raise {
  le__program_error(
    "error while parsing arguments to " + what + ": " + prin1_to_string(v),
  )
}

///|
fn le__dbind(
  d : LeDest,
  v : Value,
  fr : LeFrame,
  binds : Array[Binding],
  what : String,
) -> Unit raise {
  match d {
    DVar(p) => le__bind_param(p, v, fr, binds)
    DList(dl) => le__dbind_list(dl, v, fr, binds, what)
  }
}

///|
fn le__dbind_list(
  dl : LeDList,
  v : Value,
  fr : LeFrame,
  binds : Array[Binding],
  what : String,
) -> Unit raise {
  match dl.whole {
    Some(w) => le__dbind(w, v, fr, binds, what)
    None => ()
  }
  match dl.env_var {
    Some(p) => le__bind_param(p, Nil, fr, binds)
    None => ()
  }
  let mut l = v
  for r in dl.req {
    match l {
      Cons({ car, cdr }) => {
        le__dbind(r, car, fr, binds, what)
        l = cdr
      }
      _ => {
        le__destructure_error(what, v) |> ignore
        return
      }
    }
  }
  for o in dl.opt {
    match l {
      Cons({ car, cdr }) => {
        le__dbind(o.0, car, fr, binds, what)
        match o.2 {
          Some(sp) => le__bind_param(sp, t, fr, binds)
          None => ()
        }
        l = cdr
      }
      _ => {
        let x = match o.1 {
          Some(ic) => ic(fr)
          None => Nil
        }
        le__dbind(o.0, x, fr, binds, what)
        match o.2 {
          Some(sp) => le__bind_param(sp, Nil, fr, binds)
          None => ()
        }
      }
    }
  }
  match dl.rest {
    Some(r) => le__dbind(r, l, fr, binds, what)
    None => ()
  }
  if dl.has_key {
    for k in dl.keys {
      let found = getf_found(l, k.0)
      match found {
        Some(x) => {
          le__dbind(k.1, x, fr, binds, what)
          match k.3 {
            Some(sp) => le__bind_param(sp, t, fr, binds)
            None => ()
          }
        }
        None => {
          let x = match k.2 {
            Some(ic) => ic(fr)
            None => Nil
          }
          le__dbind(k.1, x, fr, binds, what)
          match k.3 {
            Some(sp) => le__bind_param(sp, Nil, fr, binds)
            None => ()
          }
        }
      }
    }
    ignore(dl.allow_other)
  } else if dl.rest is None && l is Cons(_) {
    le__destructure_error(what, v) |> ignore
  }
  for a in dl.aux {
    let x = match a.1 {
      Some(ic) => ic(fr)
      None => Nil
    }
    le__dbind(a.0, x, fr, binds, what)
  }
}

///|
/// Value of indicator `k` in plist `l`, if present.
fn getf_found(l : Value, k : Value) -> Value? {
  let mut p = l
  while p is Cons({ car: key, cdr: Cons({ car: v, cdr: rest }) }) {
    if eq(key, k) {
      return Some(v)
    }
    p = rest
  }
  None
}

///|
/// A destructuring lambda (macro expander): compiled lazily.
priv struct LeDLambda {
  name : String
  ll : Value
  body : Value
  env : LeEnv
  block : Value?
  mut compiled : (LeDList, LeFInfo, LeCode)?
}

///|
fn le__compile_dlambda(dl : LeDLambda) -> (LeDList, LeFInfo, LeCode) raise {
  let (specials, body) = le__parse_body(dl.body, true)
  let finfo = { size: 0 }
  let st = {
    env: Frame(finfo, dl.env),
    finfo,
    specials,
    bound: [],
    any_dyn: false,
  }
  let pat = st.dlist(dl.ll)
  let benv = le__add_free_specials(st.env, specials, st.bound)
  let bc = match dl.block {
    Some(name) => le__comp_block(name, body, benv, false)
    None => le__comp_progn(body, benv, false)
  }
  (pat, finfo, bc)
}

///|
fn le__dinvoke(
  dl : LeDLambda,
  captured : LeFrame?,
  args : Value,
  whole : Value,
) -> Value raise {
  let (pat, finfo, bc) = match dl.compiled {
    Some(c) => c
    None => {
      let c = le__compile_dlambda(dl)
      dl.compiled = Some(c)
      c
    }
  }
  let fr = { vals: Array::make(finfo.size, Value::Nil), up: captured }
  let binds : Array[Binding] = []
  defer {
    if binds.length() > 0 {
      for k = binds.length() - 1; k >= 0; k = k - 1 {
        unbind(binds[k])
      }
    }
  }
  match pat.whole {
    Some(w) => le__dbind(w, whole, fr, binds, dl.name)
    None => ()
  }
  le__dbind_list({ ..pat, whole: None }, args, fr, binds, dl.name)
  bc(fr)
}

///|
/// A macro expander function (of the form and an environment) for a
/// DEFMACRO/MACROLET definition.
fn le__make_macro_expander(
  name_v : Value,
  ll : Value,
  body : Value,
  env : LeEnv,
  fr : LeFrame?,
) -> Value {
  let name = match name_v {
    Sym(s) => s.name
    _ => "macro"
  }
  let dl : LeDLambda = { name, ll, body, env, block: Some(name_v), compiled: None }
  Func({
    name,
    call: args => {
      let form = if args.length() > 0 { args[0] } else { Nil }
      le__dinvoke(dl, fr, cdr(form), form)
    },
  })
}
