// Port of src/schatc-util.lisp: utility functions for working with M2
// pattern matching results.

///|
/// Extract the value associated with key A from association list B.
/// This is commonly used to extract matched variables from M2 pattern
/// matching results.
fn cdras(a : Value, b : Value) -> Value raise {
  cdr(assoc_equal(a, b))
}
