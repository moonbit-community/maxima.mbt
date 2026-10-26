// Port of share/contrib/elliptic_curves/modular_polynomials.lisp: the
// database of Mueller (*ec-g*) and Atkin (*ec-g1*) modular polynomials for
// primes l <= 151, used by the SEA algorithm of elliptic_curves.lisp. The
// data is in share_modular_polynomials_data.mbt (generated from the Lisp
// file by tools/gen_modular_polynomials.py).

///|
fn init_share_modular_polynomials() -> Unit raise {
  // (defvar *ec-g* (make-array 152 :element-type 'list :initial-element nil))
  if !boundp(q_ear_ec_g) {
    set(q_ear_ec_g, make_array([152])) |> ignore
  }
  if !boundp(q_ear_ec_g1) {
    set(q_ear_ec_g1, make_array([152])) |> ignore
  }
  // (setf (svref *ec-g* l) '(...) ...) and (setf (svref *ec-g1* l) ...)
  for entry in share_modular_polynomials__data {
    let (which, l, text) = entry
    let v = if which == 0 { symval(q_ear_ec_g) } else { symval(q_ear_ec_g1) }
    aset1(v, l, lread(text)) |> ignore
  }
}
