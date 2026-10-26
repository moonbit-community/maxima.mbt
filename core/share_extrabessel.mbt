// Port of share/contrib/diffequations/extrabessel.lisp (Barton Willis, 2004):
// derivatives (grad properties) of fbessel_j, fbessel_y and their derivatives,
// for odelin. The file consists of top-level
// $put and putprop forms only; they are kept in their Lisp source form
// and evaluated by `share_odeutils__eval_put_forms` at load time.

///|
let share_extrabessel__forms : String =
  #|($put '$extrabessel 1 '$version)
  #|
  #|(putprop '$fbessel_j
  #|	 '((mu x)
  #|	   ((unk) "$order" "$fbessel_j")
  #|	   (($dbessel_j) mu x))
  #|	 'grad)
  #|
  #|(putprop '$dbessel_j
  #|	 '((mu x)
  #|	   ((unk) "$order" "$dbessel_j")
  #|	   ((mtimes ) -1 ((mexpt ) x -2)
  #|	    ((mplus )
  #|	     ((mtimes )
  #|	      ((mplus ) ((mtimes ) -1 ((mexpt) mu 2))
  #|	       ((mexpt  ) x 2))
  #|	      (($fbessel_j) mu x))
  #|	     ((mtimes) x (($dbessel_j) mu x)))))
  #|	 'grad)
  #|
  #|(putprop '$fbessel_y
  #|	 '((mu x)
  #|	   ((unk) "$order" "$fbessel_y")
  #|	   (($dbessel_y) mu x))
  #|	 'grad)
  #|
  #|(putprop '$dbessel_y
  #|	 '((mu x)
  #|	   ((unk) "$order" "$dbessel_y")
  #|	   ((mtimes ) -1 ((mexpt ) x -2)
  #|	    ((mplus )
  #|	     ((mtimes )
  #|	      ((mplus ) ((mtimes ) -1 ((mexpt) mu 2))
  #|	       ((mexpt  ) x 2))
  #|	      (($fbessel_y) mu x))
  #|	     ((mtimes) x (($dbessel_y) mu x)))))
  #|	 'grad)

///|
fn init_share_extrabessel() -> Unit raise {
  share_odeutils__eval_put_forms(share_extrabessel__forms)
}
