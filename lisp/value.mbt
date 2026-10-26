///|
/// A Common Lisp value, as needed by the Maxima port.
///
/// `Nil` is both the empty list and false. `T` is the interned symbol `t`.
pub(all) enum Value {
  Nil
  Sym(Symbol)
  Cons(Cons)
  Fix(Int64)
  Big(@bigint.BigInt)
  /// A CL ratio: normalized, denominator > 1, numerator nonzero.
  Ratio(@bigint.BigInt, @bigint.BigInt)
  Flo(Double)
  /// A CL complex number; parts are real numbers of the same kind.
  Cplx(Value, Value)
  Str(String)
  Char(Char)
  Vec(LArray)
  Hash(LHash)
  Func(LFunc)
  Struct(LStruct)
  Stream(LStream)
  /// Opaque host object (e.g. closures over MoonBit data).
  Box(Ref[Any])
}

///|
/// Placeholder for opaque payloads.
pub(all) struct Any {
  tag : String
  mut data : Array[Value]
}

///|
pub(all) struct Cons {
  mut car : Value
  mut cdr : Value
}

///|
pub(all) struct Symbol {
  name : String
  id : Int
  mut value : Value
  mut bound : Bool
  mut func : LFunc?
  /// The macro or special-form handler, if this symbol names one.
  mut plist : Value
  /// The package-like home: `true` if interned.
  interned : Bool
  /// Whether this symbol is a declared constant (t, nil, keywords).
  mut constant : Bool
}

///|
/// A Lisp-callable function: takes its arguments as an array.
pub(all) struct LFunc {
  name : String
  call : (Array[Value]) -> Value raise
}

///|
/// A CL array. One-dimensional arrays use `dims = [n]`.
pub(all) struct LArray {
  mut data : Array[Value]
  mut dims : Array[Int]
  /// Fill pointer, if any.
  mut fill : Int?
  /// Element type tag: "t", "character", "fixnum", "double-float", "bit".
  elt : String
}

///|
pub(all) enum HashTest {
  Eq
  Eql
  Equal
  Equalp
} derive(Eq)

///|
pub(all) struct LHash {
  kind : HashTest
  buckets : Map[Int, Array[(Value, Value)]]
  mut count : Int
  /// Insertion order for maphash.
  mut order : Array[Value]
}

///|
/// A defstruct instance (or similar record object).
pub(all) struct LStruct {
  stype : Symbol
  slots : Array[Value]
}

///|
/// A character stream.
pub(all) struct LStream {
  /// Input buffer (for string/file input streams).
  mut input : String
  mut pos : Int
  /// Pushed-back characters (unread-char).
  unread : Array[Char]
  /// Output accumulator, if an output stream.
  out : StringBuilder?
  /// Name, for file streams.
  name : String
  /// Output sink for console streams.
  sink : ((String) -> Unit)?
  mut column : Int
  mut line : Int
  is_input : Bool
  mut eof : Bool
}

///|
pub(all) suberror LispError {
  /// CL `throw`: tag and value.
  Throw(Value, Value)
  /// A generic Lisp error with a message.
  SimpleError(String)
  /// A typed condition: condition type symbol, message, payload.
  Condition(Symbol, String, Value)
  /// `return-from` emulation: block tag and value.
  ReturnFrom(Value, Value)
  /// `go` emulation for tagbody: tag.
  Go(Value)
}

///|
pub impl Show for LispError with output(self, logger) {
  match self {
    Throw(tag, v) => logger.write_string("throw \{tag} \{v}")
    SimpleError(m) => logger.write_string(m)
    Condition(s, m, _) => logger.write_string("\{s.name}: \{m}")
    ReturnFrom(t, _) => logger.write_string("return-from \{t}")
    Go(t) => logger.write_string("go \{t}")
  }
}

///|
/// Raise a simple Lisp error.
pub fn lisp_error(msg : String) -> Value raise LispError {
  raise SimpleError(msg)
}

///|
/// Raise a simple Lisp error (generic return type).
pub fn[T] fail_with(msg : String) -> T raise LispError {
  raise SimpleError(msg)
}

///|
pub let t : Value = Sym(intern("t"))

///|
pub let nil : Value = Nil

///|
/// Convert a Bool to a Lisp boolean.
pub fn lbool(b : Bool) -> Value {
  if b {
    t
  } else {
    Nil
  }
}

///|
/// Lisp truth: anything but nil.
pub fn Value::truthy(self : Value) -> Bool {
  !(self is Nil)
}

///|
pub fn Value::is_nil(self : Value) -> Bool {
  self is Nil
}

///|
/// `(null x)`
pub fn null(x : Value) -> Bool {
  x is Nil
}

///|
/// `(not x)` as a Lisp value.
pub fn lnot(x : Value) -> Value {
  lbool(x is Nil)
}
