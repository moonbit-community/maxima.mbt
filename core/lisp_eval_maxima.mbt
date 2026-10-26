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
/// The parts of a DEFMFUN lambda list: required parameters, optional ones,
/// the rest parameter, the keyword parameters, &allow-other-keys.
priv struct LeDefmfunLL {
  req : Array[Value]
  opt : Array[Value]
  rest : Value?
  keys : Array[Value]
  allow_other : Bool
}

///|
fn le__defmfun_ll(ll : Value) -> LeDefmfunLL {
  let req = []
  let opt = []
  let mut rest = None
  let keys = []
  let mut allow_other = false
  let mut mode = 0
  for x in ll.iter() {
    match x {
      Sym({ name: "&optional", .. }) => mode = 1
      Sym({ name: "&rest" | "&body", .. }) => mode = 2
      Sym({ name: "&key", .. }) => mode = 3
      Sym({ name: "&aux", .. }) => mode = 4
      Sym({ name: "&allow-other-keys", .. }) => allow_other = true
      _ =>
        match mode {
          0 => req.push(x)
          1 => opt.push(x)
          2 => rest = Some(x)
          3 => keys.push(x)
          _ => ()
        }
    }
  }
  { req, opt, rest, keys, allow_other }
}

///|
/// The Maxima symbol `$name` for a Lisp parameter or keyword spec.
fn le__dollar_name(x : Value) -> Value raise {
  let v = match x {
    Cons({ car, .. }) => car
    _ => x
  }
  let n = match v {
    Cons({ cdr: Cons({ car: inner, .. }), .. }) => symbol_name(inner)
    _ => symbol_name(v)
  }
  sym("$" + n)
}

///|
/// DEFMFUN (defmfun-check.lisp): a `$` function gets FOO-IMPL with the
/// body and a FOO checking the number of arguments (and converting Maxima
/// keyword options `name = value`), like DEFUN-CHECKED-FORM.
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
  let add_props = [
    list4(sym("putprop"), le__quote(name), le__quote(ll), le__quote(sym("arg-list"))),
    list4(sym("defprop"), name, t, sym("translated")),
  ]
  let func_props = []
  for p in getf(opts, sym(":properties")).iter() {
    func_props.push(
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
      cons(list_star([sym("defun"), name, ll2, body]), list(add_props)),
    )
  }
  let implv = sym(le__port_name(le__port_name(sname).substring(start=1) + "-IMPL"))
  let p = le__defmfun_ll(ll)
  let keyp = p.keys.length() > 0
  let header = list1(name)
  let pretty = if p.opt.length() > 0 {
    name
  } else {
    match p.rest {
      Some(r) =>
        cons(header, append(list(p.req), list1(list2(list1(q_mlist), r))))
      None =>
        if keyp {
          let keys = []
          for k in p.keys {
            keys.push(list3(list1(q_mequal), le__dollar_name(k), cadr(k)))
          }
          cons(header, append(list(p.req), list(keys)))
        } else {
          cons(header, list(p.req))
        }
    }
  }
  let maxima_keywords = if p.allow_other {
    Value::Nil
  } else {
    let ks = []
    for k in p.keys {
      ks.push(le__dollar_name(k))
    }
    list(ks)
  }
  // (defun impl ll decls (block name (let ((%%pretty-fname 'pretty)) ...)))
  let (decls, forms) = le__split_decls(
    match body {
      Cons({ car: Str(_), cdr: Cons(_) as rest }) => rest
      _ => body
    },
  )
  let impl_body = list3(
    sym("block"),
    name,
    list_star([
      sym("let"),
      list1(list2(sym("%%pretty-fname"), le__quote(pretty))),
      list2(sym("declare"), list2(sym("ignorable"), sym("%%pretty-fname"))),
      forms,
    ]),
  )
  let out = Collector::new()
  out.add(sym("progn"))
  out.add(list_star([sym("defun"), implv, ll, append(decls, list1(impl_body))]))
  out.add(
    list([
      sym("si::defmfun-wrapper"),
      le__quote(name),
      le__quote(implv),
      le__quote(pretty),
      Fix(p.req.length().to_int64()),
      Fix(p.opt.length().to_int64()),
      lbool(p.rest is Some(_)),
      lbool(keyp),
      le__quote(maxima_keywords),
    ]),
  )
  for x in add_props {
    out.add(x)
  }
  for x in func_props {
    out.add(x)
  }
  out.add(
    list4(sym("putprop"), le__quote(name), le__quote(implv), le__quote(sym("impl-name"))),
  )
  out.result()
}

///|
fn le__register_maxima_support() -> Unit {
  le__def("si::defmfun-wrapper", a => {
    let name = le__arg(a, 0)
    let implv = le__arg(a, 1)
    let pretty = le__arg(a, 2)
    let nreq = to_int(le__arg(a, 3))
    let nopt = to_int(le__arg(a, 4))
    let restp = le__arg(a, 5).truthy()
    let keyp = le__arg(a, 6).truthy()
    let maxima_keywords = le__arg(a, 7)
    defun(name, args => {
      let nargs = args.length()
      let err = (control : String, expected : Int) => defmfun_arity_error(
        Str(control),
        pretty,
        int(expected),
        int(nargs),
        list(args),
      )
      if restp || keyp {
        if nreq > 0 && nargs < nreq {
          err("~M: expected at least ~M arguments but got ~M: ~M", nreq) |> ignore
        }
      } else if nopt > 0 {
        if nargs > nreq + nopt {
          err("~M: expected at most ~M arguments but got ~M: ~M", nreq + nopt)
          |> ignore
        }
        if nargs < nreq {
          err("~M: expected at least ~M arguments but got ~M: ~M", nreq) |> ignore
        }
      } else if nargs != nreq {
        err("~M: expected exactly ~M arguments but got ~M: ~M", nreq) |> ignore
      }
      if keyp {
        let n = nreq.min(nargs)
        let keys = defmfun_keywords(pretty, list(args[n:].to_array()), maxima_keywords)
        le__funcall(implv, args[0:n].to_array() + list_to_array(keys))
      } else {
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
  #|(defmacro symbol-array (sym) `(get ,sym 'array))
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
  #|     (if subfun-arglist
  #|      `(progn
  #|         (defprop ,verb-name ,simp-name specsimp)
  #|         (defun ,simp-name (,form-arg ,unused-arg ,z-arg)
  #|           (declare (ignore ,unused-arg))
  #|           (let ((pretty-name
  #|                   `((mqapply) ((,',verb-name array) ,',@subfun-arglist)
  #|                     ,',@lambda-list)))
  #|             (sub-arg-count-check ,(length subfun-arglist)
  #|                                  ,(length lambda-list)
  #|                                  ,form-arg
  #|                                  pretty-name))
  #|           (multiple-value-bind (,@subfun-arglist)
  #|               (values-list (mapcar #'(lambda (arg) (simpcheck arg ,z-arg))
  #|                                    (subfunsubs ,form-arg)))
  #|             (multiple-value-bind (,@lambda-list)
  #|                 (values-list (mapcar #'(lambda (arg) (simpcheck arg ,z-arg))
  #|                                      (subfunargs ,form-arg)))
  #|               (flet ((give-up (&key (fun-subs (list ,@subfun-arglist))
  #|                                     (fun-args (list ,@lambda-list)))
  #|                        (eqtest (subfunmakes ',verb-name fun-subs fun-args)
  #|                                ,form-arg)))
  #|                 ,@body)))))
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
  #|               ,@body))))))))
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
  #|(defquote dsksetq (&rest l)
  #|  (let ((dsksetp t))
  #|    (mset (car l) (eval (cadr l)))))
  #|(defquote retlist (&rest l)
  #|  (cons '(mlist simp)
  #|        (mapcar #'(lambda (z) (list '(mequal simp) z (meval z))) l)))
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
  #|(defmacro mnot_tr (operand) `(is-mnot #'identity ,operand))
  #|(defmacro mand_tr (&rest operands) (mand/mor_tr 'mand operands t nil))
  #|(defmacro mor_tr (&rest operands) (mand/mor_tr 'mor operands nil t))
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
