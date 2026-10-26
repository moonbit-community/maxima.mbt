// Lisp evaluator: Maxima's own Lisp macros and defining forms (DEFMFUN,
// DEFMSPEC, DEFMVAR, DEFPROP, DEF-SIMPLIFIER, ...) and the macros used by
// the code the translator produces (DEFMTRFUN, M-TLAMBDA, MFUNCTION-CALL,
// TRD-MSYMEVAL, MAREF/MASET, ...). Most are the definitions of the Lisp
// sources, read at initialization from `le__prelude`; DEFMFUN is written in
// MoonBit because of its argument checking.

///|
/// The port name of the CL symbol whose name is `cl_name` (CL case).
fn le__port_name(cl_name : String) -> String {
  invert_case(cl_name)
}

///|
/// Count the positional parameters of a lambda list: (required, max or -1
/// for &rest, has &key).
fn le__ll_arity(ll : Value) -> (Int, Int, Bool) {
  let mut req = 0
  let mut opt = 0
  let mut rest = false
  let mut key = false
  let mut mode = 0
  for x in ll.iter() {
    match x {
      Sym({ name: "&optional", .. }) => mode = 1
      Sym({ name: "&rest" | "&body", .. }) => {
        rest = true
        mode = 2
      }
      Sym({ name: "&key", .. }) => {
        key = true
        mode = 3
      }
      Sym({ name: "&aux", .. }) => mode = 4
      Sym({ name: "&allow-other-keys", .. }) => ()
      _ =>
        match mode {
          0 => req += 1
          1 => opt += 1
          _ => ()
        }
    }
  }
  (req, if rest { -1 } else { req + opt }, key)
}

///|
fn le__m_defmfun(form : Value, _env : LeEnv) -> Value raise {
  let spec = cadr(form)
  let ll = caddr(form)
  let body = cdddr(form)
  let (name, opts) = match spec {
    Cons({ car: n, cdr: o }) => (n, o)
    _ => (spec, Nil)
  }
  let sname = match name {
    Sym(s) => s.name
    _ => ""
  }
  let props = Collector::new()
  props.add(
    list4(sym("putprop"), le__quote(name), le__quote(ll), le__quote(sym("arg-list"))),
  )
  props.add(list4(sym("defprop"), name, t, sym("translated")))
  for p in getf(opts, sym(":properties")).iter() {
    props.add(
      list4(sym("putprop"), le__quote(name), le__quote(cadr(p)), le__quote(car(p))),
    )
  }
  let narg = ll is Sym(_)
  if !sname.has_prefix("$") || narg {
    let ll2 = if narg {
      list([
        sym("&rest"),
        sym("narg-rest-argument"),
        sym("&aux"),
        list2(ll, list2(sym("length"), sym("narg-rest-argument"))),
      ])
    } else {
      ll
    }
    return cons(
      sym("progn"),
      cons(list_star([sym("defun"), name, ll2, body]), append(props.result(), list1(le__quote(name)))),
    )
  }
  let implv = sym(le__port_name(le__port_name(sname).substring(start=1) + "-IMPL"))
  let (mn, mx, key) = le__ll_arity(ll)
  props.add(
    list4(sym("putprop"), le__quote(name), le__quote(implv), le__quote(sym("implv-name"))),
  )
  cons(
    sym("progn"),
    cons(
      list_star([sym("defun"), implv, ll, body]),
      cons(
        list([
          sym("si::defmfun-wrapper"),
          le__quote(name),
          le__quote(implv),
          Fix(mn.to_int64()),
          Fix(mx.to_int64()),
          lbool(key),
        ]),
        append(props.result(), list1(le__quote(name))),
      ),
    ),
  )
}

///|
/// Maxima callers pass keyword arguments of a DEFMFUN as `name = value`
/// equations: turn them into CL keyword arguments.
fn le__equations_to_keys(args : Array[Value], start : Int) -> Array[Value] {
  if start >= args.length() {
    return args
  }
  let out = args[0:start].to_array()
  for i in start..<args.length() {
    let a = args[i]
    if is_op(a, q_mequal) && cadr(a) is Sym(s) {
      let n = if s.name.has_prefix("$") || s.name.has_prefix("%") {
        s.name.substring(start=1)
      } else {
        s.name
      }
      out.push(sym(":" + n))
      out.push(caddr(a))
    } else {
      out.push(a)
    }
  }
  out
}

///|
fn le__register_maxima_support() -> Unit {
  le__def("si::defmfun-wrapper", a => {
    let name = le__arg(a, 0)
    let implv = le__arg(a, 1)
    let mn = to_int(le__arg(a, 2))
    let mx = to_int(le__arg(a, 3))
    let key = le__arg(a, 4).truthy()
    let sname = symbol_name(name)
    defun(name, args => {
      if key {
        // positional arguments, then keyword options
        let mut npos = 0
        while npos < args.length() &&
              !is_op(args[npos], q_mequal) &&
              !keywordp(args[npos]) {
          npos += 1
        }
        check_arity_range(sname, args[0:npos].to_array(), mn, mx)
        le__funcall(implv, le__equations_to_keys(args, npos))
      } else {
        check_arity_range(sname, args, mn, mx)
        le__funcall(implv, args)
      }
    })
    name
  })
  le__def("si::errcatch-fn", a => {
    let thunk = le__arg(a, 0)
    suprv1__errcatch(() => le__funcall(thunk, []))
  })
  le__def("si::mcatch-fn", a => {
    let thunk = le__arg(a, 0)
    suprv1__mcatch(() => le__funcall(thunk, []))
  })
  le__def("si::trd-msymeval-aux", a => {
    let l = le__arg(a, 0)
    let v = car(l)
    if boundp(v) {
      symval(v)
    } else {
      set(
        v,
        if cdr(l) is Cons(_) {
          le__eval_toplevel(cadr(l))
        } else {
          v
        },
      )
    }
  })
}

///|
/// Maxima macros defined in Lisp, after the Maxima sources (src/*.lisp),
/// with the CL symbol names written in the port's case convention.
let le__prelude : String =
  #|(defmacro defprop (sym val indic)
  #|  (if (eq indic 'expr)
  #|      `(setf (symbol-function ',sym) #',val)
  #|      `(setf (get ',sym ',indic) ',val)))
  #|(defmacro mdefprop (sym val indicator)
  #|  `(mputprop ',sym ',val ',indicator))
  #|(defmacro defun-prop (f arg &body body)
  #|  `(setf (get ',(first f) ',(second f)) #'(lambda ,arg ,@body)))
  #|(defmacro ncons (x) `(list ,x))
  #|(defmacro xcons (x y) `(cons ,y ,x))
  #|(defmacro deff (fun val) `(setf (symbol-function ',fun) ,val))
  #|(defmacro check-arg (place pred &rest res)
  #|  (when (atom pred) (setq pred (list pred place)))
  #|  `(assert ,pred (,place) ,@res))
  #|(defmacro status (option &optional item)
  #|  (cond ((equal (symbol-name option) "feature")
  #|         `(member ,(intern (string item) :keyword) *features*))
  #|        ((equal (symbol-name option) "gctime") 0)))
  #|(defmacro declare-top (&rest decl-specs)
  #|  `(eval-when (:compile-toplevel :load-toplevel :execute)
  #|     ,@(loop for decl-spec in decl-specs
  #|             when (eq (car decl-spec) 'special)
  #|             collect `(proclaim ',decl-spec))))
  #|(defmacro macsyma-module (&rest args) (declare (ignore args)) nil)
  #|(defmacro load-macsyma-macros (&rest args) (declare (ignore args)) nil)
  #|(defmacro load-macsyma-macros-at-runtime (&rest args) (declare (ignore args)) nil)
  #|(defmacro while (cond &rest body) `(do () ((not ,cond)) ,@body))
  #|(defmacro with-collector (collector-sym &body forms)
  #|  (let ((acc (gensym)))
  #|    `(let ((,acc))
  #|       (flet ((,collector-sym (x) (push x ,acc)))
  #|         ,@forms
  #|         (nreverse ,acc)))))
  #|(defmacro arg (x) `(narg1 ,x narg-rest-argument))
  #|(defmacro listify (x) `(listify1 ,x narg-rest-argument))
  #|(defmacro setarg (i val) `(setarg1 ,i ,val narg-rest-argument))
  #|(unless (fboundp 'narg1)
  #|  (defun narg1 (x l &aux tem)
  #|    (cond ((null x) (length l))
  #|          (t (setq tem (nthcdr (1- x) l))
  #|             (cond ((null tem) (error "arg ~A beyond range ~A " x (length l)))
  #|                   (t (car tem)))))))
  #|(unless (fboundp 'setarg1)
  #|  (defun setarg1 (i val l) (setf (nth (1- i) l) val) val))
  #|(unless (fboundp 'listify1)
  #|  (defun listify1 (n narg-rest-argument)
  #|    (cond ((minusp n) (copy-list (last narg-rest-argument (- n))))
  #|          ((zerop n) nil)
  #|          (t (subseq narg-rest-argument 0 n)))))
  #|(defmacro defun-maclisp (function &body body)
  #|  (when (and (car body) (symbolp (car body)))
  #|    (setf body (cons `(&rest narg-rest-argument &aux (,(car body) (length narg-rest-argument)))
  #|                     (cdr body))))
  #|  `(progn (defprop ,function t translated) (defun ,function . ,body)))
  #|(defmacro defquote (fn (aa . oth) &body rest &aux help ans)
  #|  (setq help (intern (format nil "~a-~a" fn "aux")))
  #|  (cond ((eq aa '&rest)
  #|         (setq ans
  #|               (list
  #|                `(defmacro ,fn (&rest ,(car oth))
  #|                   `(,',help ',,(car oth)))
  #|                `(defun ,help (,(car oth)) ,@rest))))
  #|        (t (setq ans
  #|                 (list
  #|                  `(defmacro ,fn (,aa . other)
  #|                     (setq other (loop for v in other collecting (list 'quote v)))
  #|                     `(,',help ',,aa ,@ other))
  #|                  `(defun ,help (,aa ,@ oth) ,@rest)))))
  #|  `(progn ,@ans))
  #|(defun si::desetq-forms (pat val)
  #|  (cond ((null pat) nil)
  #|        ((symbolp pat) (list `(setq ,pat ,val)))
  #|        (t (append (si::desetq-forms (car pat) `(car ,val))
  #|                   (si::desetq-forms (cdr pat) `(cdr ,val))))))
  #|(defun si::pattern-vars (pat)
  #|  (cond ((null pat) nil)
  #|        ((symbolp pat) (list pat))
  #|        (t (append (si::pattern-vars (car pat)) (si::pattern-vars (cdr pat))))))
  #|(defmacro desetq (&rest p)
  #|  (let ((g (gensym)))
  #|    `(let ((,g nil))
  #|       ,@(loop for (pat val) on p by #'cddr
  #|               append `((setq ,g ,val) ,@(si::desetq-forms pat g)))
  #|       ,g)))
  #|(defmacro destructuring-let (bindings &body body)
  #|  `(let ,(loop for b in bindings
  #|               append (if (and (consp b) (consp (car b)))
  #|                          (si::pattern-vars (car b))
  #|                          (list b)))
  #|     ,@(loop for b in bindings
  #|             when (and (consp b) (consp (car b)))
  #|             collect `(desetq ,(car b) ,(cadr b)))
  #|     ,@body))
  #|(defmacro destructuring-let* (bindings &body body)
  #|  `(destructuring-let ,bindings ,@body))
  #|(defmacro =0 (x) `(equal ,x 0))
  #|(defmacro =1 (x) `(equal ,x 1))
  #|(defmacro inv (x) `(power ,x -1))
  #|(defmacro inv* (x) `(power* ,x -1))
  #|(defmacro ncmul (&rest factors)
  #|  (if (= (length factors) 2)
  #|      `(ncmul2 ,@factors)
  #|      `(ncmuln (list ,@factors) t)))
  #|(defmacro take (operator &rest args) `(simplifya (list ,operator ,@args) t))
  #|(defmacro take* (operator &rest args) `(simplifya (list ,operator ,@args) nil))
  #|(defmacro ftake (name &rest args) `(simplifya (list (list ,name) ,@args) t))
  #|(defmacro ftake* (name &rest args) `(simplifya (list (list ,name) ,@args) nil))
  #|(defmacro fapply (f args) `(simplifya (cons (list ,f) ,args) t))
  #|(defmacro fapply* (f args) `(simplifya (cons (list ,f) ,args) nil))
  #|(defmacro make-mdo () '(list (list 'mdo) nil nil nil nil nil nil nil))
  #|(defmacro mdo-op (x) `(car (car ,x)))
  #|(defmacro mdo-for (x) `(second ,x))
  #|(defmacro mdo-from (x) `(third ,x))
  #|(defmacro mdo-step (x) `(fourth ,x))
  #|(defmacro mdo-next (x) `(fifth ,x))
  #|(defmacro mdo-thru (x) `(sixth ,x))
  #|(defmacro mdo-unless (x) `(seventh ,x))
  #|(defmacro mdo-body (x) `(eighth ,x))
  #|(defmacro errset (&rest l)
  #|  `(handler-case (or (multiple-value-list ,(car l)) (list nil))
  #|     (error (e) (when errset (error e)))))
  #|(defmacro errcatch (form) `(si::errcatch-fn (lambda () ,form)))
  #|(defmacro mcatch (form) `(si::mcatch-fn (lambda () ,form)))
  #|(defmacro with-$error (&body body)
  #|  `(let ((*merror-signals-$error-p* t)) ,@body))
  #|(defmacro intl::gettext (string) string)
  #|(defmacro gettext (string) string)
  #|(defmacro intl::ngettext (singular plural n)
  #|  `(if (eql ,n 1) ,singular ,plural))
  #|(defmacro intl::textdomain (domain) (declare (ignore domain)) nil)
  #|(defmacro defmspec (name-or-list &rest rest)
  #|  (destructuring-bind (function &key properties)
  #|      (if (symbolp name-or-list) (list name-or-list) name-or-list)
  #|    `(progn
  #|       (defun-prop (,function mfexpr*) ,@rest)
  #|       ,@(mapcar #'(lambda (p)
  #|                     (destructuring-bind (ind val) p
  #|                       `(putprop ',function ',val ',ind)))
  #|                 properties))))
  #|(defmacro defmvar (var &optional val doc &rest options)
  #|  (declare (ignore doc))
  #|  (let ((reset `((unless (gethash ',var *variable-initial-values*)
  #|                    (setf (gethash ',var *variable-initial-values*) ,val))))
  #|        (props nil))
  #|    (do ((opts options (rest opts)))
  #|        ((null opts))
  #|      (case (car opts)
  #|        (no-reset (setf reset nil))
  #|        (boolean
  #|         (push `(putprop ',var #'(lambda (var val)
  #|                                   (unless (member val '(t nil))
  #|                                     (mseterr var val "must be one of: true, false")))
  #|                         'assign)
  #|               props))
  #|        (:properties
  #|         (dolist (o (second opts))
  #|           (push `(putprop ',var ,(second o) ',(first o)) props))
  #|         (setf opts (rest opts)))
  #|        (:setting-predicate
  #|         (push `(putprop ',var #'(lambda (var val)
  #|                                   (multiple-value-bind (ok reason)
  #|                                       (funcall ,(second opts) val)
  #|                                     (unless ok (mseterr var val reason))))
  #|                         'assign)
  #|               props)
  #|         (setf opts (rest opts)))
  #|        (:setting-list
  #|         (push `(putprop ',var #'(lambda (var val)
  #|                                   (let ((possible-values ',(second opts)))
  #|                                     (unless (member val possible-values)
  #|                                       (mseterr var val
  #|                                                (format nil "must be one of: ~{~A~^, ~}"
  #|                                                        (mapcar #'stripdollar possible-values))))))
  #|                         'assign)
  #|               props)
  #|         (setf opts (rest opts)))
  #|        (:setter-method
  #|         (push `(putprop ',var ,(second opts) 'setter-method) props)
  #|         (setf opts (rest opts)))
  #|        ((see-also modified-commands :deprecated-p)
  #|         (setf opts (rest opts)))))
  #|    `(progn
  #|       ,@reset
  #|       (defvar ,var ,val)
  #|       ,@(nreverse props)
  #|       ',var)))
  #|(defmacro def-simplifier (base-name-and-options lambda-list &body body)
  #|  (destructuring-bind (base-name &key (simpcheck :default) (subfun-arglist nil)
  #|                                      (custom-defmfun nil) (skip-properties nil))
  #|      (if (symbolp base-name-and-options) (list base-name-and-options) base-name-and-options)
  #|    (when subfun-arglist
  #|      (error "def-simplifier: :subfun-arglist is not supported by this port's Lisp evaluator"))
  #|    (let* ((noun-name (intern (concatenate 'string "%" (string base-name))))
  #|           (verb-name (intern (concatenate 'string "$" (string base-name))))
  #|           (simp-name (intern (concatenate 'string "simp-" (string noun-name))))
  #|           (form-arg (intern "form"))
  #|           (z-arg (intern "%%simpflag"))
  #|           (unused-arg (gensym "unused-"))
  #|           (arg-forms (if (eq simpcheck :custom)
  #|                          (loop for arg in lambda-list and count from 1
  #|                                collect (list arg `(nth ,count ,form-arg)))
  #|                          (loop for arg in lambda-list and count from 1
  #|                                collect (list arg `(simpcheck (nth ,count ,form-arg) ,z-arg))))))
  #|      `(progn
  #|         ,@(unless custom-defmfun
  #|             `((defmfun ,verb-name (,@lambda-list) (ftake ',noun-name ,@lambda-list))))
  #|         ,@(unless (member 'alias skip-properties)
  #|             `((defprop ,verb-name ,noun-name alias)))
  #|         ,@(unless (member 'reversealias skip-properties)
  #|             `((defprop ,noun-name ,verb-name reversealias)))
  #|         (defprop ,noun-name ,simp-name operators)
  #|         (defprop ,noun-name ,verb-name noun)
  #|         (defprop ,verb-name ,noun-name verb)
  #|         (defun ,simp-name (,form-arg ,unused-arg ,z-arg)
  #|           (declare (ignore ,unused-arg) (ignorable ,z-arg))
  #|           (unless (= ,(length lambda-list) (length (rest ,form-arg)))
  #|             (wna-err ,form-arg ,(length lambda-list)
  #|                      `((,',noun-name) ,@(rest (dollarify ',lambda-list)))))
  #|           (let ,arg-forms
  #|             (flet ((give-up (&key (noun-name ',noun-name)
  #|                                   (args (list ,@lambda-list)))
  #|                      (eqtest (list* (list noun-name) args) ,form-arg)))
  #|               ,@body)))))))
  #|;; Translator run-time macros (transq.lisp, mdefun.lisp, transm.lisp,
  #|;; fcall.lisp, trpred.lisp).
  #|(defmacro def-mtrvar (v a &optional (priority 1))
  #|  (declare (ignore priority))
  #|  `(progn
  #|     (declare-top (special ,v))
  #|     (if (or (not (boundp ',v)) (eq ,v ',v))
  #|         (setq ,v ,a))))
  #|(defun si::skip-declare-exprs (l)
  #|  (do ((l l (cdr l)))
  #|      ((not (and (consp (car l)) (eq (caar l) 'declare))) l)))
  #|(defun si::vanilla-lambda (bvl body)
  #|  `(lambda ,bvl
  #|     (declare (special ,@bvl))
  #|     ,@(si::skip-declare-exprs body)))
  #|(defun si::rest-arg-lambda (bvl body)
  #|  (let ((req-args (butlast bvl))
  #|        (rest-arg (car (last bvl))))
  #|    `(lambda (,@req-args &rest ,rest-arg)
  #|       (declare (special ,@bvl))
  #|       (push '(mlist) ,rest-arg)
  #|       ,@(si::skip-declare-exprs body))))
  #|(defun si::lambda-with-free-vars (bvl fvl cfvl lambda-header body)
  #|  (let* ((lfvl (set-difference fvl cfvl))
  #|         (lexicals (mapcar (lambda (x) (gensym (symbol-name x))) cfvl))
  #|         (symevals (mapcar (lambda (x) `(maybe-msymeval ',x)) lfvl)))
  #|    `(let ,(mapcar #'list lexicals cfvl)
  #|       ,(funcall lambda-header bvl
  #|          `((let (,@(mapcar #'list cfvl lexicals)
  #|                  ,@(mapcar #'list lfvl symevals))
  #|              (declare (special ,@cfvl ,@lfvl))
  #|              ,@body))))))
  #|(defun si::make-tlambda (bvl fvl cfvl rest-p body)
  #|  (let ((lambda-header (if rest-p #'si::rest-arg-lambda #'si::vanilla-lambda)))
  #|    (if (null fvl)
  #|        (funcall lambda-header bvl body)
  #|        (si::lambda-with-free-vars bvl fvl cfvl lambda-header body))))
  #|(defmacro m-tlambda (bvl &rest body) (si::make-tlambda bvl '() '() nil body))
  #|(defmacro m-tlambda& (bvl &rest body) (si::make-tlambda bvl '() '() t body))
  #|(defmacro m-tlambda&env ((bvl fvl cfvl) &rest body)
  #|  (si::make-tlambda bvl fvl cfvl nil body))
  #|(defmacro m-tlambda&env& ((bvl fvl cfvl) &rest body)
  #|  (si::make-tlambda bvl fvl cfvl t body))
  #|(defmacro set-vals-into-list (argl var)
  #|  (do ((j 0 (1+ j))
  #|       (argl argl (cdr argl))
  #|       (l nil `((setf (nth ,j ,var) ,(car argl)) ,@l)))
  #|      ((null argl) `(progn ,@l))))
  #|(defmacro mfunction-call (f &rest argl)
  #|  (if (fboundp f)
  #|      `(,f ,@ argl)
  #|      `(mfunction-call-aux ',f ',argl nil)))
  #|(defmacro trd-msymeval (&rest l) `(si::trd-msymeval-aux ',l))
  #|(defmacro fungen&env-for-meval (&rest args)
  #|  `(si::fungen&env-for-meval-aux ',args))
  #|(defun si::fungen&env-for-meval-aux (args)
  #|  (let ((evl (car args)) (body (cddr args)))
  #|    `(($apply) ((mquote) ((lambda) ((mlist) ,@evl) ,@body))
  #|      ((mquote simp) ((mlist) ,@(mapcar #'eval evl))))))
  #|(defmacro maset (val ar &rest inds)
  #|  (if (or (eq ar 'mqapply) (and (consp ar) (member 'mqapply ar :test #'eq)))
  #|      `(marrayset ,val ,(car inds) ,@(cdr inds))
  #|      `(progn
  #|         (when (symbolp ,ar)
  #|           (setf ,ar (make-equal-hash-table ,(if (cdr inds) t nil))))
  #|         (maset1 ,val ,ar ,@inds))))
  #|(defmacro maref (ar &rest inds)
  #|  (cond ((or (eql ar 'mqapply) (and (consp ar) (member 'mqapply ar :test #'eq)))
  #|         `(marrayref ,(first inds) ,@(cdr inds)))
  #|        ((consp ar) `(marrayref ,ar ,(first inds) ,@(cdr inds)))
  #|        (t `(maref1 ,ar ,@inds))))
  #|(defmacro mnot_tr (operand) `(is-mnot ,operand))
  #|(defmacro mand_tr (&rest operands) `(is-mand ,@operands))
  #|(defmacro mor_tr (&rest operands) `(is-mor ,@operands))
  #|(defmacro defmtrfun ((name mode prop restp . array-flag) argl . body)
  #|  (let ((def-header)
  #|        (rest (gensym "tr-rest-arg")))
  #|    (and array-flag (setq array-flag (car array-flag)))
  #|    (setq def-header
  #|          (cond ((eq prop 'mdefine)
  #|                 (cond (array-flag `(,name a-subr))
  #|                       (t name)))
  #|                (t `(,name translated-mmacro))))
  #|    `(eval-when
  #|      (:compile-toplevel :load-toplevel :execute)
  #|      ,@(and (not array-flag) `((remprop ',name 'translate)))
  #|      ,@(and mode `((defprop ,name ,mode
  #|                      ,(cond (array-flag 'arrayfun-mode)
  #|                             (t 'function-mode)))))
  #|      ,@(cond (array-flag
  #|               `((insure-array-props ',name ',mode ',(length argl)))))
  #|      ,@(cond ((and (eq prop 'mdefine) (not array-flag))
  #|               `((cond ((status feature macsyma)
  #|                        (mputprop ',name t
  #|                                  ,(cond ((not restp)
  #|                                          ''$fixed_num_args_function)
  #|                                         (t
  #|                                          ''$variable_num_args_function)))))
  #|                 ,(cond ((not restp) nil)))))
  #|      (,(cond ((consp def-header) 'defun-prop)
  #|              (restp 'defun)
  #|              (t 'defmfun))
  #|       ,def-header ,(cond ((not restp) argl)
  #|                          (t `(&rest ,rest)))
  #|       ,@(if (not restp)
  #|             body
  #|             (let ((required-arg-count (1- (length argl))))
  #|               (if (zerop required-arg-count)
  #|                   `((let ((,(car argl) (cons '(mlist) ,rest)))
  #|                       ,@body))
  #|                   `((when (< (length ,rest) ,required-arg-count)
  #|                       (merror (intl:gettext "~M: expected at least ~M arguments but got ~M: ~M")
  #|                               ',name
  #|                               ,required-arg-count
  #|                               (length ,rest)
  #|                               (cons '(mlist) ,rest)))
  #|                     (apply (lambda ,argl ,@body)
  #|                            (nconc (subseq ,rest 0 ,required-arg-count)
  #|                                   (list (cons '(mlist) (nthcdr ,required-arg-count ,rest)))))))))))))
  #|
