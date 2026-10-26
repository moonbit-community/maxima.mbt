// Lisp evaluator: SETF and the read-modify-write macros.

///|
/// A generalized place: its subforms (each evaluated once, in order), the
/// form reading it, and the form storing a new value (returning it).
/// `simple`: the store form evaluates each subform once and does not use
/// the access form, so SETF can use the subforms directly.
priv struct LePlace {
  args : Array[Value]
  access : (Array[Value]) -> Value
  store : (Array[Value], Value) -> Value
  simple : Bool
}

///|
/// Accessors defined by DEFSTRUCT: name -> slot index.
let le__struct_accessors : Map[String, Int] = Map::new()

///|
/// DEFSETF short form: access function name -> update function.
let le__defsetf_short : Map[String, Value] = Map::new()

///|
/// DEFSETF long form: access function name -> expander function of
/// (argument variables, store variable).
let le__defsetf_long : Map[String, Value] = Map::new()

///|
fn le__call_form(head : Value, args : Array[Value]) -> Value {
  cons(head, list(args))
}

///|
fn le__store_fn_place(
  head : Value,
  args : Array[Value],
  store_fn : String,
) -> LePlace {
  {
    args,
    access: a => le__call_form(head, a),
    store: (a, v) => {
      let r = a.copy()
      r.push(v)
      le__call_form(sym(store_fn), r)
    },
    simple: true,
  }
}

///|
/// Is `name` of the form c[ad]{2,}r? Returns the letters.
fn le__cxr_letters(name : String) -> String? {
  if name.length() >= 4 && name.has_prefix("c") && name.has_suffix("r") {
    let mid = name.substring(start=1, end=name.length() - 1)
    for c in mid {
      if c != 'a' && c != 'd' {
        return None
      }
    }
    Some(mid)
  } else {
    None
  }
}

///|
fn le__place(place : Value, env : LeEnv) -> LePlace raise {
  match place {
    Sym(s) =>
      match le__lookup_var(env, s) {
        SMac(x) => le__place(x, env)
        _ =>
          {
            args: [],
            access: _ => place,
            store: (_, v) => list3(sym("setq"), place, v),
            simple: true,
          }
      }
    Cons({ car: Sym(h) as head, cdr: rest }) => {
      let args = list_to_array(rest)
      match h.name {
        "car" | "first" => return le__store_fn_place(head, args, "si::setcar")
        "cdr" | "rest" => return le__store_fn_place(head, args, "si::setcdr")
        "nth" => return le__store_fn_place(head, args, "si::setnth")
        "aref" | "svref" | "char" | "schar" | "bit" | "sbit" | "row-major-aref" =>
          return le__store_fn_place(head, args, "si::setaref")
        "elt" => return le__store_fn_place(head, args, "si::setelt")
        "gethash" => return le__store_fn_place(head, args, "si::puthash")
        "get" => return le__store_fn_place(head, args, "si::setget")
        "symbol-value" => return le__store_fn_place(head, args, "set")
        "symbol-function" | "fdefinition" =>
          return le__store_fn_place(head, args, "si::setsymfn")
        "symbol-plist" => return le__store_fn_place(head, args, "si::setplist")
        "fill-pointer" => return le__store_fn_place(head, args, "si::setfillptr")
        "mget" => return le__store_fn_place(head, args, "si::setmget")
        "macro-function" => return le__store_fn_place(head, args, "si::setmacfn")
        "the" => return le__place(cadr(rest), env)
        "second" | "third" | "fourth" | "fifth" | "sixth" | "seventh" | "eighth" | "ninth" | "tenth" => {
          let k = match h.name {
            "second" => 1
            "third" => 2
            "fourth" => 3
            "fifth" => 4
            "sixth" => 5
            "seventh" => 6
            "eighth" => 7
            "ninth" => 8
            _ => 9
          }
          return le__place(
            list2(sym("car"), list3(sym("nthcdr"), Fix(k.to_int64()), car(rest))),
            env,
          )
        }
        "getf" => {
          let inner = le__place(car(rest), env)
          let ni = inner.args.length()
          let all = inner.args.copy()
          all.push(cadr(rest))
          if cddr(rest) is Cons({ car: d, .. }) {
            all.push(d)
          }
          return {
            args: all,
            access: a => list4(
              sym("getf"),
              (inner.access)(a[0:ni].to_array()),
              a[ni],
              if a.length() > ni + 1 {
                a[ni + 1]
              } else {
                Nil
              },
            ),
            store: (a, v) => {
              let g = le__gensym("new")
              let ia = a[0:ni].to_array()
              list4(
                sym("let"),
                list1(list2(g, v)),
                (inner.store)(
                  ia,
                  list4(sym("si::putf"), (inner.access)(ia), a[ni], g),
                ),
                g,
              )
            },
            simple: false,
          }
        }
        _ => ()
      }
      match le__cxr_letters(h.name) {
        Some(letters) => {
          // (cadr x) = (car (cdr x))
          let first = letters.substring(end=1)
          let inner = "c" + letters.substring(start=1) + "r"
          return le__place(
            list2(
              sym(if first == "a" { "car" } else { "cdr" }),
              list2(sym(inner), car(rest)),
            ),
            env,
          )
        }
        None => ()
      }
      match le__struct_accessors.get(h.name) {
        Some(idx) =>
          return {
            args,
            access: a => le__call_form(head, a),
            store: (a, v) => list4(
              sym("si::setslot"),
              a[0],
              Fix(idx.to_int64()),
              v,
            ),
            simple: true,
          }
        None => ()
      }
      match le__defsetf_short.get(h.name) {
        Some(upd) => return le__store_fn_place_v(head, args, upd)
        None => ()
      }
      match le__defsetf_long.get(h.name) {
        Some(expander) =>
          return {
            args,
            access: a => le__call_form(head, a),
            store: (a, v) => {
              let gs = a.map(_ => le__gensym("a"))
              let gv = le__gensym("store")
              let binds = Collector::new()
              for i, g in gs {
                binds.add(list2(g, a[i]))
              }
              binds.add(list2(gv, v))
              let body = funcall(expander, [list(gs), gv]) catch {
                _ => Nil
              }
              list3(sym("let*"), binds.result(), body)
            },
            simple: true,
          }
        None => ()
      }
      if le__setf_functions.contains(h.name) {
        return {
          args,
          access: a => le__call_form(head, a),
          store: (a, v) => {
            let gs = a.map(_ => le__gensym("a"))
            let gv = le__gensym("new")
            let binds = Collector::new()
            for i, g in gs {
              binds.add(list2(g, a[i]))
            }
            binds.add(list2(gv, v))
            list3(
              sym("let*"),
              binds.result(),
              list_star([
                sym("funcall"),
                list2(sym("function"), list2(sym("setf"), head)),
                gv,
                list(gs),
              ]),
            )
          },
          simple: true,
        }
      }
      let (ex, expanded) = le__macroexpand_1(place, env)
      if expanded {
        return le__place(ex, env)
      }
      le__error("setf: unsupported place " + prin1_to_string(place)) |> ignore
      le__store_fn_place(head, args, "si::setcar")
    }
    _ => {
      le__error("setf: unsupported place " + prin1_to_string(place)) |> ignore
      le__store_fn_place(Nil, [], "si::setcar")
    }
  }
}

///|
/// Store function taking (args... value) given as a symbol (DEFSETF).
fn le__store_fn_place_v(head : Value, args : Array[Value], upd : Value) -> LePlace {
  {
    args,
    access: a => le__call_form(head, a),
    store: (a, v) => {
      let r = a.copy()
      r.push(v)
      le__call_form(upd, r)
    },
    simple: true,
  }
}

///|
/// Bind the place's subforms to temporaries: (bindings, temps).
fn le__place_temps(p : LePlace) -> (Array[Value], Array[Value]) {
  let binds = []
  let temps = []
  for a in p.args {
    match a {
      Nil | Fix(_) | Str(_) | Char(_) | Flo(_) => temps.push(a)
      Sym(s) if s.name.has_prefix(":") || s.name == "t" => temps.push(a)
      Cons({ car: Sym({ name: "quote", .. }), .. }) => temps.push(a)
      _ => {
        let g = le__gensym("t")
        binds.push(list2(g, a))
        temps.push(g)
      }
    }
  }
  (binds, temps)
}

///|
fn le__let_star(binds : Array[Value], body : Value) -> Value {
  if binds.length() == 0 {
    body
  } else {
    list3(sym("let*"), list(binds), body)
  }
}

///|
fn le__setf1(place : Value, v : Value, env : LeEnv) -> Value raise {
  if place is Sym(s) && !(le__lookup_var(env, s) is SMac(_)) {
    return list3(sym("setq"), place, v)
  }
  if car(place) is Sym({ name: "values", .. }) {
    // (setf (values a b) form)
    let places = list_to_array(cdr(place))
    let gs = places.map(_ => le__gensym("v"))
    let sets = Collector::new()
    for i, p in places {
      sets.add(le__setf1(p, gs[i], env))
    }
    return list_star([
      sym("multiple-value-bind"),
      list(gs),
      v,
      append(sets.result(), list1(cons(sym("values"), list(gs)))),
    ])
  }
  let p = le__place(place, env)
  if p.simple {
    (p.store)(p.args, v)
  } else {
    let (binds, temps) = le__place_temps(p)
    le__let_star(binds, (p.store)(temps, v))
  }
}

///|
fn le__m_setf(form : Value, env : LeEnv) -> Value raise {
  let r = Collector::new()
  let mut l = cdr(form)
  let mut n = 0
  while l is Cons({ car: place, cdr: Cons({ car: v, cdr: rest }) }) {
    r.add(le__setf1(place, v, env))
    n += 1
    l = rest
  }
  if l is Cons(_) {
    le__error("setf: odd number of arguments") |> ignore
  }
  if n == 1 {
    car(r.result())
  } else {
    cons(sym("progn"), r.result())
  }
}

///|
/// Read-modify-write: `f(access)` computes the new value form.
fn le__rmw(
  place : Value,
  env : LeEnv,
  pre : Array[Value],
  f : (Value) -> Value,
) -> Value raise {
  if place is Sym(s) && !(le__lookup_var(env, s) is SMac(_)) {
    return le__let_star(pre, list3(sym("setq"), place, f(place)))
  }
  let p = le__place(place, env)
  let (binds, temps) = le__place_temps(p)
  let all = pre.copy()
  for b in binds {
    all.push(b)
  }
  le__let_star(all, (p.store)(temps, f((p.access)(temps))))
}

///|
fn le__m_incf(form : Value, env : LeEnv) -> Value raise {
  let delta = if cddr(form) is Cons({ car: d, .. }) { d } else { Fix(1L) }
  le__rmw(cadr(form), env, [], a => list3(sym("+"), a, delta))
}

///|
fn le__m_decf(form : Value, env : LeEnv) -> Value raise {
  let delta = if cddr(form) is Cons({ car: d, .. }) { d } else { Fix(1L) }
  le__rmw(cadr(form), env, [], a => list3(sym("-"), a, delta))
}

///|
fn le__m_push(form : Value, env : LeEnv) -> Value raise {
  let g = le__gensym("item")
  le__rmw(caddr(form), env, [list2(g, cadr(form))], a => list3(
    sym("cons"),
    g,
    a,
  ))
}

///|
fn le__m_pushnew(form : Value, env : LeEnv) -> Value raise {
  let g = le__gensym("item")
  let keys = cdddr(form)
  le__rmw(caddr(form), env, [list2(g, cadr(form))], a => list_star([
    sym("adjoin"),
    g,
    a,
    keys,
  ]))
}

///|
fn le__m_pop(form : Value, env : LeEnv) -> Value raise {
  let place = cadr(form)
  let g = le__gensym("list")
  if place is Sym(s) && !(le__lookup_var(env, s) is SMac(_)) {
    return list3(
      sym("let"),
      list1(list2(g, place)),
      list3(
        sym("prog1"),
        list2(sym("car"), g),
        list3(sym("setq"), place, list2(sym("cdr"), g)),
      ),
    )
  }
  let p = le__place(place, env)
  let (binds, temps) = le__place_temps(p)
  binds.push(list2(g, (p.access)(temps)))
  le__let_star(
    binds,
    list3(
      sym("prog1"),
      list2(sym("car"), g),
      (p.store)(temps, list2(sym("cdr"), g)),
    ),
  )
}

///|
fn le__m_remf(form : Value, env : LeEnv) -> Value raise {
  let place = cadr(form)
  let ind = caddr(form)
  let gi = le__gensym("ind")
  let gn = le__gensym("new")
  let gf = le__gensym("found")
  let p = le__place(place, env)
  let (binds, temps) = le__place_temps(p)
  binds.push(list2(gi, ind))
  le__let_star(
    binds,
    list4(
      sym("multiple-value-bind"),
      list2(gn, gf),
      list3(sym("si::remf"), (p.access)(temps), gi),
      list3(sym("progn"), (p.store)(temps, gn), gf),
    ),
  )
}

///|
fn le__m_shiftf(form : Value, env : LeEnv) -> Value raise {
  let items = list_to_array(cdr(form))
  let newval = items[items.length() - 1]
  let places = items[0:items.length() - 1].to_array()
  let binds = []
  let ps : Array[(LePlace, Array[Value])] = []
  let olds = []
  for pl in places {
    let p = le__place(pl, env)
    let (b, temps) = le__place_temps(p)
    for x in b {
      binds.push(x)
    }
    let g = le__gensym("old")
    binds.push(list2(g, (p.access)(temps)))
    olds.push(g)
    ps.push((p, temps))
  }
  let stores = Collector::new()
  for i, pt in ps {
    let v = if i + 1 < ps.length() { olds[i + 1] } else { newval }
    stores.add((pt.0.store)(pt.1, v))
  }
  stores.add(olds[0])
  le__let_star(binds, cons(sym("progn"), stores.result()))
}

///|
fn le__m_rotatef(form : Value, env : LeEnv) -> Value raise {
  let places = list_to_array(cdr(form))
  if places.length() < 2 {
    return Nil
  }
  let binds = []
  let ps : Array[(LePlace, Array[Value])] = []
  let olds = []
  for pl in places {
    let p = le__place(pl, env)
    let (b, temps) = le__place_temps(p)
    for x in b {
      binds.push(x)
    }
    let g = le__gensym("old")
    binds.push(list2(g, (p.access)(temps)))
    olds.push(g)
    ps.push((p, temps))
  }
  let stores = Collector::new()
  for i, pt in ps {
    stores.add((pt.0.store)(pt.1, olds[(i + 1) % ps.length()]))
  }
  stores.add(Nil)
  le__let_star(binds, cons(sym("progn"), stores.result()))
}

///|
/// (si::modify-place place fn args...): place = (fn place args...)
fn le__m_modify_place(form : Value, env : LeEnv) -> Value raise {
  let fn_ = caddr(form)
  let args = cdddr(form)
  le__rmw(cadr(form), env, [], a => list_star([fn_, a, args]))
}

///|
fn le__m_defsetf(form : Value, _env : LeEnv) -> Value raise {
  let name = cadr(form)
  match cddr(form) {
    Cons({ car: Sym(_) as upd, .. }) =>
      list3(sym("si::defsetf-short"), le__quote(name), le__quote(upd))
    Cons({ car: ll, cdr: Cons({ car: stores, cdr: body }) }) =>
      // (defsetf name ll (store) body): expander (lambda (args store) ...)
      list3(
        sym("si::defsetf-long"),
        le__quote(name),
        list3(
          sym("lambda"),
          list2(sym("si::args"), sym("si::store")),
          list4(
            sym("destructuring-bind"),
            ll,
            sym("si::args"),
            list_star([
              sym("let"),
              list1(list2(car(stores), sym("si::store"))),
              body,
            ]),
          ),
        ),
      )
    _ => Nil
  }
}
