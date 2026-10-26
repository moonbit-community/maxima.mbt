///|
/// `(make-hash-table :test test)`
pub fn make_hash_table(kind? : HashTest = Eql) -> Value {
  Hash({ kind, buckets: Map::new(), count: 0, order: [] })
}

///|
fn LHash::hash_of(self : LHash, k : Value) -> Int {
  match self.kind {
    Eq | Eql =>
      match k {
        Sym(s) => s.id
        Fix(n) => n.to_int()
        Char(c) => c.to_int()
        // identity keys: their contents can change, so hash only by kind
        // (numbers are compared by value under EQL)
        Cons(_) => 101
        Str(_) => 103
        Vec(_) => 107
        Struct(s) => s.stype.id * 31 + 109
        Hash(_) => 113
        Func(_) => 127
        Stream(_) | Box(_) => 131
        _ => hash_equal(k)
      }
    Equal | Equalp =>
      match k {
        Str(s) => if self.kind == Equalp { s.to_lower().hash() } else { s.hash() }
        _ => hash_equal(k)
      }
  }
}

///|
fn LHash::same(self : LHash, a : Value, b : Value) -> Bool {
  match self.kind {
    Eq => eq(a, b)
    Eql => eql(a, b)
    Equal => equal(a, b)
    Equalp => equalp(a, b)
  }
}

///|
/// `(gethash k table)` -> value or None.
pub fn LHash::get(self : LHash, k : Value) -> Value? {
  let h = self.hash_of(k)
  match self.buckets.get(h) {
    Some(b) => {
      for e in b {
        if self.same(e.0, k) {
          return Some(e.1)
        }
      }
      None
    }
    None => None
  }
}

///|
/// `(setf (gethash k table) v)`
pub fn LHash::set(self : LHash, k : Value, v : Value) -> Unit {
  let h = self.hash_of(k)
  match self.buckets.get(h) {
    Some(b) => {
      for i, e in b {
        if self.same(e.0, k) {
          b[i] = (e.0, v)
          return
        }
      }
      b.push((k, v))
    }
    None => self.buckets[h] = [(k, v)]
  }
  self.count += 1
  self.order.push(k)
}

///|
/// `(remhash k table)`
pub fn LHash::remove(self : LHash, k : Value) -> Bool {
  let h = self.hash_of(k)
  match self.buckets.get(h) {
    Some(b) =>
      for i, e in b {
        if self.same(e.0, k) {
          b.remove(i) |> ignore
          self.count -= 1
          return true
        }
      }
    None => ()
  }
  false
}

///|
/// Entries in insertion order.
pub fn LHash::entries(self : LHash) -> Array[(Value, Value)] {
  let r = []
  // compact the order log, skipping removed/duplicated keys
  let seen = make_hash_table(kind=self.kind)
  let neworder = []
  for k in self.order {
    match self.get(k) {
      Some(v) =>
        match seen {
          Hash(sh) =>
            if sh.get(k) is None {
              sh.set(k, t)
              r.push((k, v))
              neworder.push(k)
            }
          _ => ()
        }
      None => ()
    }
  }
  self.order = neworder
  r
}

///|
pub fn LHash::clear(self : LHash) -> Unit {
  self.buckets.clear()
  self.count = 0
  self.order = []
}

///|
fn as_hash(table : Value) -> LHash raise LispError {
  match table {
    Hash(h) => h
    _ => raise type_error(table, "hash-table")
  }
}

///|
/// `(gethash k table)` -> value (nil if absent).
pub fn gethash(k : Value, table : Value) -> Value raise LispError {
  as_hash(table).get(k).unwrap_or(Nil)
}

///|
/// `(gethash k table)` -> (value, present-p).
pub fn gethash2(k : Value, table : Value) -> (Value, Bool) raise LispError {
  match as_hash(table).get(k) {
    Some(v) => (v, true)
    None => (Nil, false)
  }
}

///|
/// `(setf (gethash k table) v)`; returns v.
pub fn sethash(k : Value, table : Value, v : Value) -> Value raise LispError {
  as_hash(table).set(k, v)
  v
}

///|
/// `(remhash k table)`
pub fn remhash(k : Value, table : Value) -> Bool raise LispError {
  as_hash(table).remove(k)
}

///|
/// `(clrhash table)`
pub fn clrhash(table : Value) -> Value raise LispError {
  as_hash(table).clear()
  table
}

///|
/// `(hash-table-count table)`
pub fn hash_table_count(table : Value) -> Int raise LispError {
  as_hash(table).count
}

///|
/// `(maphash f table)`
pub fn maphash(
  f : (Value, Value) -> Unit raise,
  table : Value,
) -> Unit raise {
  for e in as_hash(table).entries() {
    f(e.0, e.1)
  }
}

///|
/// `(hash-table-p x)`
pub fn hash_table_p(x : Value) -> Bool {
  x is Hash(_)
}
