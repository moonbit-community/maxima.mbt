// Lisp evaluator: the LOOP macro (the commonly used subset of the ANSI
// LOOP facility).
//
// Expansion:
//   (block name
//     (let* (variables...)
//       (tagbody
//         initially-forms
//        si::loop-top
//         per-iteration code of the clauses, in order (FOR clauses step on
//         every iteration but the first, then test for termination)
//         (setq first nil)
//         (go si::loop-top)
//        si::loop-end
//         finally-forms
//         (return-from name result))))

///|
priv struct LeLoop {
  toks : Array[Value]
  mut i : Int
  mut name : Value
  bindings : Array[Value]
  prologue : Array[Value]
  body : Array[Value]
  epilogue : Array[Value]
  first : Value
  mut result : Value
  mut default_acc : Value?
  mut default_tail : Value?
  mut default_kind : String
  // named accumulators: var -> tail var
  acc_tails : Map[String, Value]
}

///|
fn le__loop_kw(x : Value) -> String {
  match x {
    Sym(s) => if s.name.has_prefix(":") { s.name.substring(start=1) } else { s.name }
    _ => ""
  }
}

///|
fn LeLoop::peek_kw(self : LeLoop) -> String {
  if self.i < self.toks.length() {
    le__loop_kw(self.toks[self.i])
  } else {
    ""
  }
}

///|
fn LeLoop::next(self : LeLoop) -> Value raise {
  if self.i >= self.toks.length() {
    le__error("loop: unexpected end of clauses") |> ignore
    return Nil
  }
  let x = self.toks[self.i]
  self.i += 1
  x
}

///|
fn LeLoop::at_end(self : LeLoop) -> Bool {
  self.i >= self.toks.length()
}

///|
fn LeLoop::kw_is(self : LeLoop, names : Array[String]) -> Bool {
  let k = self.peek_kw()
  names.contains(k)
}

///|
/// Skip an optional type spec after a loop variable.
fn LeLoop::skip_type(self : LeLoop) -> Unit {
  let k = self.peek_kw()
  if k == "of-type" {
    self.i += 2
  } else if [
      "fixnum", "float", "t", "integer", "number", "flonum", "double-float", "single-float",
      "real", "string", "list", "symbol",
    ].contains(k) {
    self.i += 1
  }
}

///|
/// Variables of a (possibly destructuring) loop variable pattern.
fn le__loop_pattern_vars(pat : Value, out : Array[Value]) -> Unit {
  match pat {
    Nil => ()
    Sym(_) => out.push(pat)
    Cons({ car, cdr }) => {
      le__loop_pattern_vars(car, out)
      le__loop_pattern_vars(cdr, out)
    }
    _ => ()
  }
}

///|
/// Forms assigning the parts of `val` (a variable) to a pattern.
fn le__loop_destructure(pat : Value, val : Value, out : Array[Value]) -> Unit {
  match pat {
    Nil => ()
    Sym(_) => out.push(list3(sym("setq"), pat, val))
    Cons({ car, cdr }) => {
      le__loop_destructure(car, list2(sym("car"), val), out)
      le__loop_destructure(cdr, list2(sym("cdr"), val), out)
    }
    _ => ()
  }
}

///|
fn LeLoop::bind_pattern(self : LeLoop, pat : Value, init : Value) -> Unit {
  match pat {
    Sym(_) => self.bindings.push(list2(pat, init))
    _ => {
      let vars = []
      le__loop_pattern_vars(pat, vars)
      for v in vars {
        self.bindings.push(list2(v, Nil))
      }
      if !(init is Nil) {
        let g = le__gensym("init")
        self.bindings.push(list2(g, init))
        let sets = []
        le__loop_destructure(pat, g, sets)
        for s in sets {
          self.prologue.push(s)
        }
      }
    }
  }
}

///|
fn LeLoop::assign(self : LeLoop, pat : Value, val : Value, out : Array[Value]) -> Unit {
  ignore(self)
  match pat {
    Sym(_) => out.push(list3(sym("setq"), pat, val))
    _ => {
      let g = le__gensym("v")
      let sets = []
      le__loop_destructure(pat, g, sets)
      out.push(list_star([sym("let"), list1(list2(g, val)), list(sets)]))
    }
  }
}

///|
fn le__loop_go_end() -> Value {
  list2(sym("go"), sym("si::loop-end"))
}

///|
fn LeLoop::not_first(self : LeLoop, forms : Array[Value]) -> Value {
  cons(sym("unless"), cons(self.first, list(forms)))
}

///|
fn LeLoop::parse_for(self : LeLoop) -> Unit raise {
  let pat = self.next()
  self.skip_type()
  let kw = self.peek_kw()
  self.i += 1
  match kw {
    "in" | "on" => {
      let lst = self.next()
      let mut by : Value = Nil
      if self.peek_kw() == "by" {
        self.i += 1
        by = self.next()
      }
      let g = le__gensym("list")
      self.bindings.push(list2(g, lst))
      if kw == "in" {
        let vars = []
        le__loop_pattern_vars(pat, vars)
        for v in vars {
          self.bindings.push(list2(v, Nil))
        }
      } else if !(pat is Sym(_)) {
        let vars = []
        le__loop_pattern_vars(pat, vars)
        for v in vars {
          self.bindings.push(list2(v, Nil))
        }
      } else {
        self.bindings.push(list2(pat, Nil))
      }
      let step = if by is Nil {
        list2(sym("cdr"), g)
      } else {
        list3(sym("funcall"), by, g)
      }
      self.body.push(self.not_first([list3(sym("setq"), g, step)]))
      self.body.push(list3(sym("when"), list2(sym("atom"), g), le__loop_go_end()))
      let out = []
      if kw == "in" {
        self.assign(pat, list2(sym("car"), g), out)
      } else {
        self.assign(pat, g, out)
      }
      for o in out {
        self.body.push(o)
      }
    }
    "=" => {
      let e1 = self.next()
      if self.peek_kw() == "then" {
        self.i += 1
        let e2 = self.next()
        let vars = []
        le__loop_pattern_vars(pat, vars)
        for v in vars {
          self.bindings.push(list2(v, Nil))
        }
        let out = []
        self.assign(pat, list4(sym("if"), self.first, e1, e2), out)
        for o in out {
          self.body.push(o)
        }
      } else {
        let vars = []
        le__loop_pattern_vars(pat, vars)
        for v in vars {
          self.bindings.push(list2(v, Nil))
        }
        let out = []
        self.assign(pat, e1, out)
        for o in out {
          self.body.push(o)
        }
      }
    }
    "across" => {
      let vec = self.next()
      let gv = le__gensym("vec")
      let gi = le__gensym("i")
      self.bindings.push(list2(gv, vec))
      self.bindings.push(list2(gi, Fix(0L)))
      let vars = []
      le__loop_pattern_vars(pat, vars)
      for v in vars {
        self.bindings.push(list2(v, Nil))
      }
      self.body.push(self.not_first([list3(sym("setq"), gi, list2(sym("1+"), gi))]))
      self.body.push(
        list3(
          sym("when"),
          list3(sym(">="), gi, list2(sym("length"), gv)),
          le__loop_go_end(),
        ),
      )
      let out = []
      self.assign(pat, list3(sym("aref"), gv, gi), out)
      for o in out {
        self.body.push(o)
      }
    }
    "being" => {
      // being {the|each} {hash-keys|hash-values|...} {of|in} h [using (...)]
      if ["the", "each"].contains(self.peek_kw()) {
        self.i += 1
      }
      let what = self.peek_kw()
      self.i += 1
      if ["of", "in"].contains(self.peek_kw()) {
        self.i += 1
      }
      let src = self.next()
      let mut other : Value = Nil
      if self.peek_kw() == "using" {
        self.i += 1
        other = cadr(self.next())
      }
      let g = le__gensym("list")
      let (lst, key) = match what {
        "hash-key" | "hash-keys" => (list2(sym("si::hash-table-pairs"), src), true)
        "hash-value" | "hash-values" =>
          (list2(sym("si::hash-table-pairs"), src), false)
        "symbol" | "symbols" | "present-symbol" | "present-symbols" | "external-symbol" | "external-symbols" =>
          (list1(sym("si::all-symbols")), true)
        "element" | "elements" => (list2(sym("si::sequence-list"), src), true)
        _ => {
          le__error("loop: unsupported iteration being " + what) |> ignore
          (Nil, true)
        }
      }
      let pairs = what.has_prefix("hash")
      self.bindings.push(list2(g, lst))
      self.bindings.push(list2(pat, Nil))
      if !(other is Nil) {
        self.bindings.push(list2(other, Nil))
      }
      self.body.push(self.not_first([list3(sym("setq"), g, list2(sym("cdr"), g))]))
      self.body.push(list3(sym("when"), list2(sym("atom"), g), le__loop_go_end()))
      if pairs {
        let (mine, theirs) = if key { ("car", "cdr") } else { ("cdr", "car") }
        self.body.push(
          list3(sym("setq"), pat, list2(sym(mine), list2(sym("car"), g))),
        )
        if !(other is Nil) {
          self.body.push(
            list3(sym("setq"), other, list2(sym(theirs), list2(sym("car"), g))),
          )
        }
      } else {
        self.body.push(list3(sym("setq"), pat, list2(sym("car"), g)))
      }
    }
    _ => {
      // arithmetic: from/upfrom/downfrom start, to/upto/below/downto/above limit, by step
      self.i -= 1
      let mut start : Value = Fix(0L)
      let mut limit : Value? = None
      let mut step : Value = Fix(1L)
      let mut down = false
      let mut inclusive = true
      while true {
        match self.peek_kw() {
          "from" | "upfrom" => {
            self.i += 1
            start = self.next()
          }
          "downfrom" => {
            self.i += 1
            start = self.next()
            down = true
          }
          "to" | "upto" => {
            self.i += 1
            limit = Some(self.next())
          }
          "below" => {
            self.i += 1
            limit = Some(self.next())
            inclusive = false
          }
          "downto" => {
            self.i += 1
            limit = Some(self.next())
            down = true
          }
          "above" => {
            self.i += 1
            limit = Some(self.next())
            down = true
            inclusive = false
          }
          "by" => {
            self.i += 1
            step = self.next()
          }
          _ => break
        }
      }
      let var_ = pat
      self.bindings.push(list2(var_, start))
      let gstep = le__gensym("step")
      self.bindings.push(list2(gstep, step))
      let lim = match limit {
        Some(l) => {
          let gl = le__gensym("limit")
          self.bindings.push(list2(gl, l))
          Some(gl)
        }
        None => None
      }
      self.body.push(
        self.not_first([
          list3(sym("setq"), var_, list3(sym(if down { "-" } else { "+" }), var_, gstep)),
        ]),
      )
      match lim {
        Some(gl) => {
          let cmp = match (down, inclusive) {
            (false, true) => ">"
            (false, false) => ">="
            (true, true) => "<"
            (true, false) => "<="
          }
          self.body.push(
            list3(sym("when"), list3(sym(cmp), var_, gl), le__loop_go_end()),
          )
        }
        None => ()
      }
    }
  }
}

///|
/// The accumulation variable for a clause: `into var` or the default.
fn LeLoop::acc_var(self : LeLoop, kind : String) -> (Value, Value?) raise {
  if self.peek_kw() == "into" {
    self.i += 1
    let v = self.next()
    let name = match v {
      Sym(s) => s.name
      _ => ""
    }
    if !self.acc_tails.contains(name) {
      let tail = le__gensym("tail")
      self.acc_tails[name] = tail
      let init = match kind {
        "sum" | "count" => Value::Fix(0L)
        _ => Value::Nil
      }
      self.bindings.push(list2(v, init))
      self.bindings.push(list2(tail, Nil))
    }
    (v, self.acc_tails.get(name))
  } else {
    match self.default_acc {
      Some(a) => (a, self.default_tail)
      None => {
        let a = le__gensym("acc")
        let tail = le__gensym("tail")
        let init = match kind {
          "sum" | "count" => Value::Fix(0L)
          _ => Value::Nil
        }
        self.bindings.push(list2(a, init))
        self.bindings.push(list2(tail, Nil))
        self.default_acc = Some(a)
        self.default_tail = Some(tail)
        self.default_kind = kind
        self.result = a
        (a, Some(tail))
      }
    }
  }
}

///|
fn le__loop_subst_it(x : Value, it : Value?) -> Value {
  match (x, it) {
    (Sym({ name: "it", .. }), Some(g)) => g
    _ => x
  }
}

///|
/// Parse one main clause; returns its forms.
fn LeLoop::parse_clause(self : LeLoop, it : Value?) -> Array[Value] raise {
  let kw = self.peek_kw()
  self.i += 1
  match kw {
    "do" | "doing" => {
      let r = []
      while !self.at_end() && self.toks[self.i] is Cons(_) {
        r.push(self.toks[self.i])
        self.i += 1
      }
      r
    }
    "collect" | "collecting" | "append" | "appending" | "nconc" | "nconcing" => {
      let x = le__loop_subst_it(self.next(), it)
      let (acc, tail) = self.acc_var("list")
      let tl = match tail {
        Some(t) => t
        None => le__gensym("tail")
      }
      let g = le__gensym("new")
      let newcells = match kw {
        "collect" | "collecting" => list2(sym("list"), x)
        "append" | "appending" => list2(sym("copy-list"), x)
        _ => x
      }
      // (let ((g new)) (when g (if tail (rplacd tail g) (setq acc g)) (setq tail (last g))))
      [
        list3(
          sym("let"),
          list1(list2(g, newcells)),
          list4(
            sym("when"),
            g,
            list4(
              sym("if"),
              tl,
              list3(sym("rplacd"), list2(sym("last"), tl), g),
              list3(sym("setq"), acc, g),
            ),
            list3(sym("setq"), tl, list2(sym("last"), g)),
          ),
        ),
      ]
    }
    "sum" | "summing" => {
      let x = le__loop_subst_it(self.next(), it)
      let (acc, _) = self.acc_var("sum")
      [list3(sym("setq"), acc, list3(sym("+"), acc, x))]
    }
    "count" | "counting" => {
      let x = le__loop_subst_it(self.next(), it)
      let (acc, _) = self.acc_var("count")
      [list3(sym("when"), x, list3(sym("setq"), acc, list2(sym("1+"), acc)))]
    }
    "maximize" | "maximizing" | "minimize" | "minimizing" => {
      let x = le__loop_subst_it(self.next(), it)
      let (acc, _) = self.acc_var("max")
      let g = le__gensym("v")
      let op = if kw.has_prefix("max") { "max" } else { "min" }
      [
        list3(
          sym("let"),
          list1(list2(g, x)),
          list3(
            sym("setq"),
            acc,
            list4(sym("if"), acc, list3(sym(op), acc, g), g),
          ),
        ),
      ]
    }
    "while" => [list3(sym("unless"), self.next(), le__loop_go_end())]
    "until" => [list3(sym("when"), self.next(), le__loop_go_end())]
    "always" => {
      self.result = t
      [list3(sym("unless"), self.next(), list3(sym("return-from"), self.name, Nil))]
    }
    "never" => {
      self.result = t
      [list3(sym("when"), self.next(), list3(sym("return-from"), self.name, Nil))]
    }
    "thereis" => {
      let g = le__gensym("v")
      [
        list3(
          sym("let"),
          list1(list2(g, self.next())),
          list3(sym("when"), g, list3(sym("return-from"), self.name, g)),
        ),
      ]
    }
    "return" => {
      let x = le__loop_subst_it(self.next(), it)
      [list3(sym("return-from"), self.name, x)]
    }
    "when" | "if" | "unless" => {
      let test_form = self.next()
      let g = le__gensym("it")
      let then_ = self.parse_conditional_body(Some(g))
      let mut else_ : Array[Value] = []
      if self.peek_kw() == "else" {
        self.i += 1
        else_ = self.parse_conditional_body(Some(g))
      }
      if self.peek_kw() == "end" {
        self.i += 1
      }
      let tst = if kw == "unless" { list2(sym("not"), g) } else { g }
      [
        list3(
          sym("let"),
          list1(list2(g, test_form)),
          list4(
            sym("if"),
            tst,
            cons(sym("progn"), list(then_)),
            cons(sym("progn"), list(else_)),
          ),
        ),
      ]
    }
    _ => {
      le__error("loop: unknown clause " + prin1_to_string(self.toks[self.i - 1]))
      |> ignore
      []
    }
  }
}

///|
fn LeLoop::parse_conditional_body(self : LeLoop, it : Value?) -> Array[Value] raise {
  let r = []
  for x in self.parse_clause(it) {
    r.push(x)
  }
  while self.peek_kw() == "and" {
    self.i += 1
    for x in self.parse_clause(it) {
      r.push(x)
    }
  }
  r
}

///|
fn le__m_loop(form : Value, _env : LeEnv) -> Value raise {
  let toks = list_to_array(cdr(form))
  // simple loop: (loop form...)
  if toks.iter().all(x => x is Cons(_)) {
    let top = le__gensym("top")
    return list3(
      sym("block"),
      Nil,
      cons(sym("tagbody"), cons(top, append(list(toks), list1(list2(sym("go"), top))))),
    )
  }
  let first = le__gensym("first")
  let lp = {
    toks,
    i: 0,
    name: Nil,
    bindings: [list2(first, t)],
    prologue: [],
    body: [],
    epilogue: [],
    first,
    result: Nil,
    default_acc: None,
    default_tail: None,
    default_kind: "",
    acc_tails: {},
  }
  if lp.peek_kw() == "named" {
    lp.i += 1
    lp.name = lp.next()
  }
  while !lp.at_end() {
    match lp.peek_kw() {
      "with" => {
        lp.i += 1
        while true {
          let pat = lp.next()
          lp.skip_type()
          let mut init : Value = Nil
          if lp.peek_kw() == "=" {
            lp.i += 1
            init = lp.next()
          }
          lp.bind_pattern(pat, init)
          if lp.peek_kw() == "and" {
            lp.i += 1
          } else {
            break
          }
        }
      }
      "for" | "as" => {
        lp.i += 1
        lp.parse_for()
        while lp.peek_kw() == "and" {
          lp.i += 1
          lp.parse_for()
        }
      }
      "repeat" => {
        lp.i += 1
        let g = le__gensym("count")
        lp.bindings.push(list2(g, lp.next()))
        lp.body.push(
          list3(sym("when"), list3(sym("<="), g, Fix(0L)), le__loop_go_end()),
        )
        lp.body.push(list3(sym("setq"), g, list2(sym("1-"), g)))
      }
      "initially" => {
        lp.i += 1
        while !lp.at_end() && lp.toks[lp.i] is Cons(_) {
          lp.prologue.push(lp.toks[lp.i])
          lp.i += 1
        }
      }
      "finally" => {
        lp.i += 1
        while !lp.at_end() && lp.toks[lp.i] is Cons(_) {
          lp.epilogue.push(lp.toks[lp.i])
          lp.i += 1
        }
      }
      _ =>
        for x in lp.parse_clause(None) {
          lp.body.push(x)
        }
    }
  }
  let tb = Collector::new()
  for x in lp.prologue {
    tb.add(x)
  }
  tb.add(sym("si::loop-top"))
  for x in lp.body {
    tb.add(x)
  }
  tb.add(list3(sym("setq"), first, Nil))
  tb.add(list2(sym("go"), sym("si::loop-top")))
  tb.add(sym("si::loop-end"))
  for x in lp.epilogue {
    tb.add(x)
  }
  tb.add(list3(sym("return-from"), lp.name, lp.result))
  list3(
    sym("block"),
    lp.name,
    list3(sym("let*"), list(lp.bindings), cons(sym("tagbody"), tb.result())),
  )
}
