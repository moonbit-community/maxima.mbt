// The arithmetic of the bigfloat-package COBYLA (bf_cobyla.mbt,
// bf_cobylb.mbt, bf_trstlp.mbt, translated from share/cobyla/lisp/bf-*.lisp
// by tools/f2cl2mbt.py --lib=bf-cobyla).  Those files are the f2cl output
// edited to run in Maxima's BIGFLOAT package, whose + - * / < ... ABS SQRT
// MAX MIN EXPT COERCE are generic over CL reals and BIGFLOAT objects.  The
// routines are generic over a type T implementing this trait; Maxima's
// instance (core) wraps a Lisp value and calls numeric.lisp's generic
// functions, so a value keeps its dynamic type (a double stays a double
// until combined with a bigfloat) exactly as in the Lisp.

///|
pub(open) trait BfReal {
  /// A CL double-float / integer as a value.
  from_double(Double) -> Self
  from_int(Int) -> Self
  /// The two-argument generic arithmetic.
  add(Self, Self) -> Self raise
  sub(Self, Self) -> Self raise
  mul(Self, Self) -> Self raise
  div(Self, Self) -> Self raise
  neg(Self) -> Self raise
  expt(Self, Self) -> Self raise
  /// The two-argument comparisons.
  lt(Self, Self) -> Bool raise
  gt(Self, Self) -> Bool raise
  le(Self, Self) -> Bool raise
  ge(Self, Self) -> Bool raise
  eq(Self, Self) -> Bool raise
  /// `(max a b)`, `(min a b)`
  max(Self, Self) -> Self raise
  min(Self, Self) -> Self raise
  abs(Self) -> Self raise
  sqrt(Self) -> Self raise
  /// `(coerce x 'bigfloat)`
  coerce_bigfloat(Self) -> Self raise
  /// The text of the value under a FORMAT directive of the Fortran output
  /// (`~w,d,e,k,'o,,'E/bigfloat:format-e/`).
  format_directive(Self, String) -> String
  /// The user routine CALCFC(N, M, X, F, CON), which the Lisp calls by name:
  /// returns F; CON is a section (with its offset) of COBYLA's work array.
  calcfc(Int, Int, Array[Self], Self, Array[Self], Int) -> Self raise
}
