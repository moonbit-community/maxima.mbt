// The Value-level SLATEC/QUADPACK routines (core/slatec_values.mbt) called
// from interpreted Lisp. The expected values are what the reference Maxima
// (SBCL, f2cl Lisp) prints for the same forms.

///|
test "slatec values: functions and multiple values" {
  inspect(
    le_test("(multiple-value-list (slatec::derf 0.5d0))"),
    content="(0.5204998778130465 nil)",
  )
  inspect(
    le_test("(multiple-value-list (slatec::dgamln 2.5d0 0))"),
    content="(0.2846828704729182 nil 0)",
  )
  inspect(
    le_test("(multiple-value-list (slatec::zsqrt$ 1d0 2d0 0d0 0d0))"),
    content="(nil nil 1.2720196495140688 0.7861513777574234)",
  )
  inspect(
    le_test("(multiple-value-list (slatec::zairy 1d0 2d0 0 1 0d0 0d0 0 0))"),
    content="(nil nil nil nil -0.2193862549814275 -0.17538591140810952 0 0)",
  )
  inspect(
    le_test("(multiple-value-list (slatec::j4save 2 0 nil))"),
    content="(2 nil nil nil)",
  )
  inspect(le_test("(multiple-value-list (slatec::fdump))"), content="nil")
  inspect(le_test("(multiple-value-list (slatec::xerhlt \"x\"))"), content="(nil)")
  inspect(
    le_test(
      "(multiple-value-list (slatec::xgetua (make-array 5 :element-type 'f2cl-lib:integer4) 0))",
    ),
    content="(nil 1)",
  )
  // wrong argument types signal a TYPE-ERROR, as in SBCL
  inspect(
    le_test(
      "(handler-case (slatec::derf 1) (type-error () 'type-error))",
    ),
    content="type-error",
  )
  inspect(
    le_test(
      "(handler-case (slatec::dgamln 2.5d0 nil) (type-error () 'type-error))",
    ),
    content="type-error",
  )
}

///|
test "slatec values: output arrays" {
  inspect(
    le_test(
      "(let ((a (make-array 5 :element-type 'double-float))) (list (multiple-value-list (slatec::dbesj 1.5d0 0.25d0 3 a 0)) a))",
    ),
    content="((nil nil nil nil 0) #(0.619213908826832 0.47477058613775636 0.17207040140276186 0.0 0.0))",
  )
  inspect(
    le_test(
      "(let ((r (make-array 2 :element-type 'double-float)) (i (make-array 2 :element-type 'double-float))) (list (multiple-value-list (slatec::zbesj 1d0 2d0 0.5d0 1 2 r i 0 0)) r i))",
    ),
    content="((nil nil nil nil nil nil nil 0 0) #(1.9866134730419236 0.3313593472237321) #(0.0013808728354310906 1.1610671990114145))",
  )
  // the same array passed for two parameters stays one array
  inspect(
    le_test(
      "(let ((r (make-array 2 :element-type 'double-float)) (i (make-array 2 :element-type 'double-float))) (list (multiple-value-list (slatec::zbesy 1d0 2d0 0.5d0 1 2 r i 0 r i 0)) r i))",
    ),
    content="((nil nil nil nil nil nil nil 0 nil nil 0) #(-0.0 -0.0) #(0.0 0.0))",
  )
  inspect(
    le_test(
      "(let ((b (make-array 3 :element-type 'double-float :initial-contents '(1d0 2d0 3d0)))) (slatec::dgtsl 3 (make-array 3 :element-type 'double-float :initial-contents '(0d0 1d0 1d0)) (make-array 3 :element-type 'double-float :initial-contents '(4d0 4d0 4d0)) (make-array 3 :element-type 'double-float :initial-contents '(1d0 1d0 0d0)) b 0) b)",
    ),
    content="#(0.17857142857142855 0.28571428571428575 0.6785714285714285)",
  )
  // an array of the wrong element type
  inspect(
    le_test(
      "(handler-case (slatec::dbesj 1.5d0 0.25d0 3 (make-array 3 :initial-element 0d0) 0) (type-error () 'type-error))",
    ),
    content="type-error",
  )
}

///|
test "slatec values: function arguments" {
  inspect(
    le_test(
      "(let ((iw (make-array 10 :element-type 'f2cl-lib:integer4)) (w (make-array 40 :element-type 'double-float))) (list (multiple-value-list (slatec::dqags #'(lambda (x) (/ (sqrt x))) 0d0 1d0 0d0 1d-8 0d0 0d0 0 0 10 40 0 iw w)) iw (subseq w 0 8)))",
    ),
    content="((nil nil nil nil nil 1.9999999999999984 5.773159728050814e-15 231 0 nil nil 6 nil nil) #(1 2 3 4 5 6 0 0 0 0) #(0.0 0.5 0.25 0.125 0.0625 0.03125 0.0 0.0))",
  )
  inspect(
    le_test(
      "(multiple-value-list (slatec::dqags 'sin 0d0 1d0 0d0 1d-8 0d0 0d0 0 0 10 40 0 (make-array 10 :element-type 'f2cl-lib:integer4) (make-array 40 :element-type 'double-float)))",
    ),
    content="(nil nil nil nil nil 0.45969769413186023 5.103669643922841e-15 21 0 nil nil 1 nil nil)",
  )
  // the integrand's errors propagate
  inspect(
    le_test(
      "(handler-case (slatec::dqags #'(lambda (x) (error \"boom\")) 0d0 1d0 0d0 1d-8 0d0 0d0 0 0 10 40 0 (make-array 10 :element-type 'f2cl-lib:integer4) (make-array 40 :element-type 'double-float)) (error (e) (format nil \"~a\" e)))",
    ),
    content="\"boom\"",
  )
  // DASYJY with DJAIRY / DYAIRY as FUNJY
  inspect(
    le_test(
      "(let ((y (make-array 3 :element-type 'double-float)) (wk (make-array 7 :element-type 'double-float))) (list (multiple-value-list (slatec::dasyjy #'slatec::djairy 30d0 25.5d0 1d0 3 y wk 0)) y wk))",
    ),
    content="((nil nil nil nil nil nil nil 0) #(0.133794296566741 0.02737402961280024 -0.08908338153250107) #(-0.6296966953372569 0.7935343063392136 0.12274831359300453 2.8845853694356065 1.6295144593890007 -2.6553173733578275 2.8643271579912155))",
  )
  inspect(
    le_test(
      "(let ((y (make-array 3 :element-type 'double-float)) (wk (make-array 7 :element-type 'double-float))) (list (multiple-value-list (slatec::dasyjy 'slatec::dyairy 30d0 25.5d0 -1d0 3 y wk 0)) y wk))",
    ),
    content="((nil nil nil nil nil nil nil 0) #(0.14710740847452236 0.061378125810979914 -0.038672719541788934) #(-0.19008264462809898 0.43598468393751977 0.024846821615172248 0.6832875944172344 1.0082423410384194 -1.0165526182626323 3.0184053683988394))",
  )
  // DQK15W with a weight function
  inspect(
    le_test(
      "(multiple-value-list (slatec::dqk15w #'(lambda (x) (* x x)) #'slatec::dqwgtc 2d0 0d0 0d0 0d0 1 0d0 1d0 0d0 0d0 0d0 0d0))",
    ),
    content="(nil nil 2.0 0.0 0.0 0.0 1 nil nil -0.2725887222397812 4.169052992620414e-12 0.2725887222397812 0.23312618226325837)",
  )
  inspect(
    le_test(
      "(multiple-value-list (slatec::dqk15w #'(lambda (x) (* x x)) #'(lambda (x c p2 p3 p4 kp) 1) 2d0 0d0 0d0 0d0 1 0d0 1d0 0d0 0d0 0d0 0d0))",
    ),
    content="(nil nil 2.0 0.0 0.0 0.0 1 nil nil 0.33333333333333326 3.700743415417189e-15 0.33333333333333326 0.25689389466806084)",
  )
}
