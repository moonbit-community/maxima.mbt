///|
let symbol_table : Map[String, Symbol] = Map::new(capacity=32768)

///|
let symbol_counter : Ref[Int] = Ref(0)

///|
let gensym_counter : Ref[Int] = Ref(1000)

///|
fn new_symbol(name : String, interned : Bool) -> Symbol {
  symbol_counter.val += 1
  {
    name,
    id: symbol_counter.val,
    value: Nil,
    bound: false,
    func: None,
    plist: Nil,
    interned,
    constant: false,
  }
}

///|
/// Intern a symbol by its exact name. Lisp-level names are lower case as
/// written in the Lisp source (`mplus`, `$sin`, `%pi`, `*expandp*`).
pub fn intern(name : String) -> Symbol {
  match symbol_table.get(name) {
    Some(s) => s
    None => {
      let s = new_symbol(name, true)
      symbol_table[name] = s
      if name == "t" || name.has_prefix(":") {
        s.value = Sym(s)
        s.bound = true
        s.constant = true
      }
      s
    }
  }
}

///|
/// Intern and wrap as a Value.
pub fn sym(name : String) -> Value {
  if name == "nil" {
    Nil
  } else {
    Sym(intern(name))
  }
}

///|
/// Look up a symbol without creating it.
pub fn find_symbol(name : String) -> Value {
  match symbol_table.get(name) {
    Some(s) => Sym(s)
    None => Nil
  }
}

///|
/// Create an uninterned symbol.
pub fn make_symbol(name : String) -> Value {
  Sym(new_symbol(name, false))
}

///|
/// `(gensym)` / `(gensym "PREFIX")`
pub fn gensym(prefix? : String = "g") -> Value {
  gensym_counter.val += 1
  Sym(new_symbol(prefix + gensym_counter.val.to_string(), false))
}

///|
/// Iterate all interned symbols.
pub fn all_symbols() -> Array[Symbol] {
  symbol_table.values().collect()
}

///|
pub fn Symbol::to_value(self : Symbol) -> Value {
  Sym(self)
}

///|
/// `(symbolp x)` — nil and t are symbols.
pub fn symbolp(x : Value) -> Bool {
  x is (Nil | Sym(_))
}

///|
/// The symbol name of a symbol value (nil is "nil").
pub fn symbol_name(x : Value) -> String raise LispError {
  match x {
    Nil => "nil"
    Sym(s) => s.name
    _ => raise SimpleError("symbol-name: not a symbol: \{x}")
  }
}

///|
/// Return the Symbol inside a value; raises for non-symbols (including nil).
pub fn as_symbol(x : Value) -> Symbol raise LispError {
  match x {
    Sym(s) => s
    Nil => intern("nil")
    _ => raise SimpleError("not a symbol: \{x}")
  }
}

// ---------------------------------------------------------------------------
// Property lists

///|
/// `(get sym prop)`
pub fn get(s : Value, prop : Value) -> Value {
  match s {
    Sym(sy) => plist_get(sy.plist, prop)
    _ => Nil
  }
}

///|
/// `(get sym prop default)`
pub fn get_default(s : Value, prop : Value, default : Value) -> Value {
  match s {
    Sym(sy) =>
      loop sy.plist {
        Cons({ car: k, cdr: Cons({ car: v, cdr: rest }) }) =>
          if eq(k, prop) {
            break v
          } else {
            continue rest
          }
        _ => break default
      }
    _ => default
  }
}

///|
fn plist_get(pl : Value, prop : Value) -> Value {
  loop pl {
    Cons({ car: k, cdr: Cons({ car: v, cdr: rest }) }) =>
      if eq(k, prop) {
        break v
      } else {
        continue rest
      }
    _ => break Nil
  }
}

///|
/// `(putprop sym val prop)` — Maclisp argument order; returns val.
pub fn putprop(s : Value, v : Value, prop : Value) -> Value {
  match s {
    Sym(sy) => {
      let mut p = sy.plist
      while p is Cons(c) {
        if eq(c.car, prop) {
          match c.cdr {
            Cons(vc) => {
              vc.car = v
              return v
            }
            _ => break
          }
        }
        p = match c.cdr {
          Cons(vc) => vc.cdr
          _ => Nil
        }
      }
      sy.plist = Cons({ car: prop, cdr: Cons({ car: v, cdr: sy.plist }) })
      v
    }
    _ => v
  }
}

///|
/// `(setf (get sym prop) val)` — returns val.
pub fn setf_get(s : Value, prop : Value, v : Value) -> Value {
  putprop(s, v, prop)
}

///|
/// `(remprop sym prop)` — returns non-nil if a property was removed.
pub fn remprop(s : Value, prop : Value) -> Value {
  match s {
    Sym(sy) => {
      let mut prev : Cons? = None
      let mut p = sy.plist
      while p is Cons(c) {
        let next = match c.cdr {
          Cons(vc) => vc.cdr
          _ => Nil
        }
        if eq(c.car, prop) {
          match prev {
            None => sy.plist = next
            Some(pc) =>
              match pc.cdr {
                Cons(pvc) => pvc.cdr = next
                _ => ()
              }
          }
          return t
        }
        prev = Some(c)
        p = next
      }
      Nil
    }
    _ => Nil
  }
}

///|
/// `(symbol-plist s)`
pub fn symbol_plist(s : Value) -> Value {
  match s {
    Sym(sy) => sy.plist
    _ => Nil
  }
}

///|
/// `(setf (symbol-plist s) pl)`
pub fn set_symbol_plist(s : Value, pl : Value) -> Value {
  match s {
    Sym(sy) => sy.plist = pl
    _ => ()
  }
  pl
}

// ---------------------------------------------------------------------------
// Value cells

///|
/// `(symbol-value s)`; raises if unbound.
pub fn symbol_value(s : Value) -> Value raise LispError {
  match s {
    Nil => Nil
    Sym(sy) =>
      if sy.bound {
        sy.value
      } else {
        raise Condition(
          intern("unbound-variable"),
          "The variable \{sy.name} is unbound.",
          s,
        )
      }
    _ => raise SimpleError("symbol-value: not a symbol")
  }
}

///|
/// Read a special variable's value; returns nil if unbound. This is the
/// workhorse accessor for translated special-variable reads.
pub fn symval(s : Value) -> Value {
  match s {
    Sym(sy) => sy.value
    _ => Nil
  }
}

///|
/// `(setq s v)` / `(set s v)` on a special variable; returns v.
pub fn set(s : Value, v : Value) -> Value {
  match s {
    Sym(sy) => {
      sy.value = v
      sy.bound = true
    }
    _ => ()
  }
  v
}

///|
/// `(boundp s)`
pub fn boundp(s : Value) -> Bool {
  match s {
    Nil => true
    Sym(sy) => sy.bound
    _ => false
  }
}

///|
/// `(makunbound s)`
pub fn makunbound(s : Value) -> Value {
  match s {
    Sym(sy) => {
      sy.bound = false
      sy.value = Nil
    }
    _ => ()
  }
  s
}

///|
/// Saved state of a special binding.
pub(all) struct Binding {
  sym : Symbol
  old : Value
  was_bound : Bool
}

///|
/// Dynamically bind a special variable. Pair with `unbind` (use `defer`).
pub fn bind(s : Value, v : Value) -> Binding {
  let sy = match s {
    Sym(sy) => sy
    _ => intern("nil")
  }
  let b = { sym: sy, old: sy.value, was_bound: sy.bound }
  sy.value = v
  sy.bound = true
  b
}

///|
/// Restore a binding made by `bind`.
pub fn unbind(b : Binding) -> Unit {
  b.sym.value = b.old
  b.sym.bound = b.was_bound
}

///|
/// Bind several specials at once.
pub fn bind_all(pairs : Array[(Value, Value)]) -> Array[Binding] {
  pairs.map(p => bind(p.0, p.1))
}

///|
/// Restore bindings made by `bind_all`, in reverse order.
pub fn unbind_all(bs : Array[Binding]) -> Unit {
  for i = bs.length() - 1; i >= 0; i = i - 1 {
    unbind(bs[i])
  }
}

///|
/// `(let ((s v)) body)` for a special `s`.
pub fn[T] with_special(s : Value, v : Value, f : () -> T raise) -> T raise {
  let b = bind(s, v)
  defer unbind(b)
  f()
}

///|
/// `(let ((s1 v1) (s2 v2) ...) body)` for specials.
pub fn[T] with_specials(
  pairs : Array[(Value, Value)],
  f : () -> T raise,
) -> T raise {
  let bs = bind_all(pairs)
  defer unbind_all(bs)
  f()
}

///|
/// `(progv syms vals body)`
pub fn[T] progv(syms : Value, vals : Value, f : () -> T raise) -> T raise {
  let pairs = []
  let mut s = syms
  let mut v = vals
  while s is Cons(c) {
    let val = match v {
      Cons(vc) => {
        v = vc.cdr
        vc.car
      }
      _ => Nil
    }
    pairs.push((c.car, val))
    s = c.cdr
  }
  with_specials(pairs, f)
}

// ---------------------------------------------------------------------------
// Function cells

///|
/// `(fboundp s)`
pub fn fboundp(s : Value) -> Bool {
  match s {
    Sym(sy) => sy.func is Some(_)
    _ => false
  }
}

///|
/// `(symbol-function s)` as a Value.
pub fn symbol_function(s : Value) -> Value raise LispError {
  match s {
    Sym({ func: Some(f), .. }) => Func(f)
    _ => raise Condition(intern("undefined-function"), "undefined function \{s}", s)
  }
}

///|
/// Define a function cell.
pub fn defun(
  s : Value,
  f : (Array[Value]) -> Value raise,
  name? : String,
) -> Unit {
  match s {
    Sym(sy) => sy.func = Some({ name: name.unwrap_or(sy.name), call: f })
    _ => ()
  }
}

///|
/// `(fmakunbound s)`
pub fn fmakunbound(s : Value) -> Value {
  match s {
    Sym(sy) => sy.func = None
    _ => ()
  }
  s
}

///|
/// Wrap a MoonBit closure as a Lisp function value.
pub fn lfunc(name : String, f : (Array[Value]) -> Value raise) -> Value {
  Func({ name, call: f })
}

///|
/// `(funcall f args...)`: f is a symbol or function value.
pub fn funcall(f : Value, args : Array[Value]) -> Value raise {
  match f {
    Func(lf) => (lf.call)(args)
    Sym({ func: Some(lf), .. }) => (lf.call)(args)
    Sym(sy) =>
      raise Condition(
        intern("undefined-function"),
        "The function \{sy.name} is undefined.",
        f,
      )
    _ => raise SimpleError("funcall: not a function: \{f}")
  }
}

///|
/// `(apply f arglist)`
pub fn apply(f : Value, arglist : Value) -> Value raise {
  funcall(f, list_to_array(arglist))
}

///|
pub fn funcall0(f : Value) -> Value raise {
  funcall(f, [])
}

///|
pub fn funcall1(f : Value, a : Value) -> Value raise {
  funcall(f, [a])
}

///|
pub fn funcall2(f : Value, a : Value, b : Value) -> Value raise {
  funcall(f, [a, b])
}

///|
pub fn funcall3(f : Value, a : Value, b : Value, c : Value) -> Value raise {
  funcall(f, [a, b, c])
}

///|
/// `(functionp x)`
pub fn functionp(x : Value) -> Bool {
  x is Func(_)
}

///|
/// Keyword symbol `:name`.
pub fn kw(name : String) -> Value {
  sym(":" + name)
}

///|
/// `(keywordp x)`
pub fn keywordp(x : Value) -> Bool {
  match x {
    Sym(s) => s.name.has_prefix(":")
    _ => false
  }
}
