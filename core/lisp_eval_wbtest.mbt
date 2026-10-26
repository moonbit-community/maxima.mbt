///|
/// Evaluate Lisp source text; the printed value of the last form.
fn le_test(src : String) -> String raise {
  initialize()
  prin1_to_string(lisp_eval_string(src))
}

///|
/// The printed values of every form, separated by " | ".
fn le_test_all(src : String) -> String raise {
  initialize()
  le__init()
  let r = []
  @lisp.lread_source_all(src, f => r.push(prin1_to_string(le__eval_file_form(f))))
  r.join(" | ")
}

///|
test "lisp eval: special forms and closures" {
  inspect(le_test("(let ((x 1) (y 2)) (+ x y))"), content="3")
  inspect(le_test("(let* ((x 1) (y (+ x 1))) (list x y))"), content="(1 2)")
  inspect(
    le_test("(labels ((f (n) (if (<= n 1) 1 (* n (f (1- n)))))) (f 20))"),
    content="2432902008176640000",
  )
  inspect(
    le_test(
      "(let ((fns nil)) (dotimes (i 3) (let ((j i)) (push (lambda () j) fns))) (mapcar #'funcall fns))",
    ),
    content="(2 1 0)",
  )
  inspect(
    le_test("(let ((c 0)) (flet ((inc () (incf c))) (inc) (inc) c))"),
    content="2",
  )
  inspect(le_test("(block b (return-from b 7) 8)"), content="7")
  inspect(
    le_test("(let ((n 0)) (tagbody top (incf n) (when (< n 5) (go top))) n)"),
    content="5",
  )
  inspect(le_test("(catch 'x (throw 'x 42) 1)"), content="42")
  inspect(
    le_test(
      "(let ((l nil)) (catch 'q (unwind-protect (throw 'q 1) (push 'done l))) l)",
    ),
    content="(done)",
  )
  inspect(le_test("((lambda (x &optional (y 2)) (list x y)) 1)"), content="(1 2)")
  inspect(le_test("(funcall '(lambda (x) (* x 3)) 4)"), content="12")
  inspect(
    le_test("(macrolet ((sq (x) `(* ,x ,x))) (symbol-macrolet ((y 5)) (sq y)))"),
    content="25",
  )
  inspect(le_test("(progv '(*pv*) '(99) (symbol-value '*pv*))"), content="99")
  // a non-local exit through a closure
  inspect(
    le_test("(block out (mapc (lambda (x) (when (> x 1) (return-from out x))) '(1 2 3)) nil)"),
    content="2",
  )
}

///|
test "lisp eval: lambda lists and multiple values" {
  inspect(
    le_test_all(
      "(defun kf (a &optional (b 10 bp) &rest r &key (c 3 cp) &allow-other-keys) (list a b bp r c cp)) (kf 1) (kf 1 2 :c 4) (kf 1 2 :d 5)",
    ),
    content="kf | (1 10 nil nil 3 nil) | (1 2 t (:c 4) 4 t) | (1 2 t (:d 5) 3 nil)",
  )
  inspect(
    le_test("(destructuring-bind (a (b c) &optional d &key e) '(1 (2 3) 4 :e 5) (list a b c d e))"),
    content="(1 2 3 4 5)",
  )
  inspect(
    le_test("(multiple-value-bind (a b c) (values 1 2) (list a b c))"),
    content="(1 2 nil)",
  )
  inspect(le_test("(multiple-value-list (floor 7 2))"), content="(3 1)")
  inspect(
    le_test("(multiple-value-call #'list (values 1 2) (values) (values 3))"),
    content="(1 2 3)",
  )
  inspect(
    le_test_all(
      "(defun two (x) (values x (* x x))) (multiple-value-list (two 5)) (defun one () (let ((q (floor 5 2))) q)) (multiple-value-list (one))",
    ),
    content="two | (5 25) | one | (2)",
  )
  inspect(le_test("(nth-value 1 (gethash 'nope (make-hash-table)))"), content="nil")
  inspect(
    le_test("(multiple-value-list (multiple-value-prog1 (values 1 2) (values 3 4)))"),
    content="(1 2)",
  )
}

///|
test "lisp eval: specials and declarations" {
  inspect(
    le_test_all(
      "(defvar *sp* 1) (defun get-sp () *sp*) (let ((*sp* 2)) (get-sp)) (get-sp)",
    ),
    content="*sp* | get-sp | 2 | 1",
  )
  // a Maxima special (DEFMVAR in the sources) is bound dynamically
  inspect(
    le_test("(let (($ratprint nil)) (symbol-value '$ratprint))"),
    content="nil",
  )
  inspect(
    le_test(
      "(defun sp-user () (declare (special zz)) zz) (let ((zz 7)) (declare (special zz)) (sp-user))",
    ),
    content="7",
  )
  inspect(
    le_test("(handler-case (progn (declare (special x)) 1) (error () 'error))"),
    content="error",
  )
}

///|
test "lisp eval: macros, backquote and setf" {
  inspect(
    le_test_all(
      "(defmacro my-inc (place &optional (d 1)) `(setf ,place (+ ,place ,d))) (let ((x 5)) (my-inc x 3) x)",
    ),
    content="my-inc | 8",
  )
  inspect(
    le_test("(let ((x 1) (l '(2 3))) `(a ,x ,@l b (c ,(+ x 1)) . d))"),
    content="(a 1 2 3 b (c 2) . d)",
  )
  inspect(le_test("(let ((x 'y)) `(a `(b ,,x)))"), content="(a `(b ,y))")
  inspect(
    le_test("(let ((b '(x y))) `(a `(c ,,@b)))"),
    content="(a `(c ,x ,y))",
  )
  inspect(
    le_test("(let ((l (list 1 2 3))) (setf (car l) 'a (cadr l) 'b (nth 2 l) 'c) l)"),
    content="(a b c)",
  )
  inspect(
    le_test(
      "(let ((h (make-hash-table :test 'equal))) (setf (gethash \"k\" h) 1) (incf (gethash \"k\" h) 10) (gethash \"k\" h))",
    ),
    content="11",
  )
  inspect(
    le_test("(let ((pl (list :a 1))) (setf (getf pl :b) 2) (setf (getf pl :a) 3) pl)"),
    content="(:b 2 :a 3)",
  )
  inspect(
    le_test("(let ((l (list nil nil))) (push 'x (cadr l)) (pushnew 'x (cadr l)) l)"),
    content="(nil (x))",
  )
  inspect(
    le_test("(let ((a 1) (b 2) (c 3)) (rotatef a b c) (list a b c (shiftf a 9)))"),
    content="(2 3 1 2)",
  )
  inspect(
    le_test("(let ((v (make-array 3 :initial-element 0))) (incf (aref v 1) 5) v)"),
    content="#(0 5 0)",
  )
}

///|
test "lisp eval: loop and iteration" {
  inspect(le_test("(loop for i from 1 to 10 when (evenp i) collect i)"), content="(2 4 6 8 10)")
  inspect(le_test("(loop for x in '(1 2 3) for y = (* x x) sum y)"), content="14")
  inspect(
    le_test("(loop for (a b) in '((1 2) (3 4)) collect (+ a b))"),
    content="(3 7)",
  )
  inspect(
    le_test(
      "(loop for x in '(1 2 3 4) if (oddp x) collect x into odds else collect x into evens finally (return (list odds evens)))",
    ),
    content="((1 3) (2 4))",
  )
  inspect(
    le_test("(loop named outer for i from 1 do (loop for j from 1 do (when (> (* i j) 6) (return-from outer (list i j)))))"),
    content="(1 7)",
  )
  inspect(le_test("(loop for x = 1 then (* x 2) while (< x 100) collect x)"), content="(1 2 4 8 16 32 64)")
  inspect(le_test("(do ((i 0 (1+ i)) (acc nil (cons i acc))) ((= i 4) acc))"), content="(3 2 1 0)")
  inspect(le_test("(prog ((x 0)) top (incf x) (if (< x 3) (go top)) (return x))"), content="3")
  inspect(
    le_test("(let ((s 0)) (dolist (x '(1 2 3) s) (incf s x)))"),
    content="6",
  )
}

///|
test "lisp eval: conditions and structures" {
  inspect(
    le_test("(handler-case (error \"boom ~a\" 1) (error (e) (format nil \"caught: ~a\" e)))"),
    content="\"caught: boom 1\"",
  )
  inspect(le_test("(handler-case (car 5) (type-error () 'te))"), content="te")
  inspect(le_test("(handler-case (/ 1 0) (division-by-zero () 'div0))"), content="div0")
  inspect(
    le_test(
      "(define-condition my-err (error) ((data :initarg :data :reader my-err-data)) (:report (lambda (c s) (format s \"my-err ~a\" (my-err-data c))))) (handler-case (error 'my-err :data 42) (my-err (c) (list (my-err-data c) (princ-to-string c))))",
    ),
    content="(42 \"my-err 42\")",
  )
  inspect(
    le_test(
      "(let ((log nil)) (handler-bind ((warning (lambda (c) (push (princ-to-string c) log) (muffle-warning c)))) (warn \"w1\")) log)",
    ),
    content="(\"w1\")",
  )
  // a Maxima error is a condition of type maxima-$error
  inspect(
    le_test("(let ((*merror-signals-$error-p* t)) (handler-case (merror \"bad\") (maxima-$error () 'merror)))"),
    content="merror",
  )
  inspect(
    le_test(
      "(defstruct point x (y 0)) (let ((p (make-point :x 1))) (setf (point-y p) 5) (incf (point-x p)) (list (point-x p) (point-y p) (point-p p) (point-p 3)))",
    ),
    content="(2 5 t nil)",
  )
  inspect(
    le_test("(defstruct (lpt (:type list) :named) a b) (make-lpt :a 1 :b 2)"),
    content="(lpt 1 2)",
  )
}

///|
test "lisp eval: Maxima defining forms" {
  // DEFMFUN: Maxima's argument checking and keyword options
  inspect(
    le_test_all(
      "(defmfun $le_twice (x &optional (y 1)) (mul 2 x y)) (mfuncall '$le_twice 3) (get '$le_twice 'impl-name)",
    ),
    content="le_twice-impl | 6 | le_twice-impl",
  )
  inspect(
    le_test(
      "(list (errcatch (funcall '$le_twice 1 2 3)) (cadr $error) (cdddr $error))",
    ),
    content="(nil \"~M: expected at most ~M arguments but got ~M: ~M\" (2 3 ((mlist) 1 2 3)))",
  )
  // DEFMSPEC receives the unevaluated form
  inspect(
    le_test_all("(defmspec $le_quoted (l) (cadr l)) (meval '(($le_quoted) $undefined_xyz))"),
    content="#<FUNCTION lambda> | $undefined_xyz",
  )
  inspect(
    le_test("(defprop $le_p 42 le-ind) (get '$le_p 'le-ind)"),
    content="42",
  )
  inspect(le_test("(take '(%sin) 0)"), content="0")
  inspect(le_test("(ftake '%cos 0)"), content="1")
}

///|
test "lisp eval: translator output" {
  // forms as translate_file writes them (from the reference Maxima)
  inspect(
    le_test_all(
      #|(progn (defprop $le_g t translated) (add2lnc '$le_g $props)
      #|  (defmtrfun ($le_g $any mdefine nil nil) ($n) (declare (special $n))
      #|    ((lambda ($s) (declare (special $s))
      #|       (do (($i 1. (+ 1. $i))) ((let (($prederror t)) ($is-boole-eval (simplify (list '(mgreaterp) $i $n)))) '$done)
      #|         (declare (special $i))
      #|         (let () (declare (special $s)) (if (not (boundp '$s)) (add2lnc '$s $values)) (setq $s (add* $s $i))))
      #|       $s) 0)))
      #|(mfuncall '$le_g 10)
      #|(progn (defprop $le_k t translated) (add2lnc '$le_k $props)
      #|  (defmtrfun ($le_k $any mdefine nil nil) ($a) (declare (special $a))
      #|    (m-tlambda&env (($u) ($a) nil) (declare (special $u)) (add* $u $a))))
      #|(funcall (mfuncall '$le_k 5) 2)
      #|(progn (defprop $le_h t translated) (add2lnc '$le_h $props)
      #|  (defmtrfun ($le_h $any mdefine t nil) ($x $y) (declare (special $y $x)) ($cons $x $y)))
      #|(mfuncall '$le_h 1 2 3)
      ,
    ),
    content="le_g-impl | 55 | le_k-impl | ((mplus simp) 2 $a) | $le_h | ((mlist simp) 1 2 3)",
  )
}

///|
test "lisp eval: Maxima-level entry points" {
  initialize()
  // ?-call of a Lisp macro, and a Lisp lambda expression applied by Maxima
  lisp_eval_string("(defvar le-test-list nil)") |> ignore
  inspect(
    prin1_to_string(meval(maxima_lit("?push(1, ?le\\-test\\-list)"))),
    content="(1)",
  )
  inspect(
    prin1_to_string(
      mapply1(lread("(lambda (x) (* x 10))"), list1(Fix(4L)), Nil, Nil),
    ),
    content="40",
  )
  inspect(
    prin1_to_string(d_eval_string_lisp(Str("(+ 1 2) (values 4 5)")).0),
    content="((mlist simp) 4 5)",
  )
}
