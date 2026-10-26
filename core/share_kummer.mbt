// Port of share/contrib/diffequations/kummer.lisp (Barton Willis, 2004):
// derivatives (grad properties) of kummer_m, kummer_u and their derivatives,
// for odelin. The file consists of top-level
// $put and putprop forms only; they are kept in their Lisp source form
// and evaluated by `share_odeutils__eval_put_forms` at load time.

///|
let share_kummer__forms : String =
  #|($put '$kummer 1 '$version)
  #|
  #|(putprop '$kummer_m
  #|	 '((a b x)
  #|	   ((unk) "$order" "$kummer_m")
  #|	   ((unk) "$order" "$kummer_m")
  #|	   (($dkummer_m) a b x))
  #|	 'grad)
  #|	 
  #|(putprop '$dkummer_m
  #|	 '((a b x)
  #|	   ((unk) "$order" "$kummer_m")
  #|	   ((unk) "$order" "$kummer_m")
  #|	   ((mtimes ) ((mexpt  ) x -1)
  #|	    ((mplus ) ((mtimes  ) a 
  #|		       (($kummer_m ) a b x))
  #|	     ((mtimes  ) -1 (($dkummer_m ) a b x) b)
  #|	     ((mtimes  ) (($dkummer_m ) a b x) x))))
  #|	 'grad)
  #|
  #|(putprop '$kummer_u
  #|	 '((a b x)
  #|	   ((unk) "$order" "$kummer_u")
  #|	   ((unk) "$order" "$kummer_u")
  #|	   (($dkummer_u) a b x))
  #|	 'grad)
  #|
  #|(putprop '$dkummer_u
  #|	 '((a b x)
  #|	   ((unk) "$order" "$dkummer_u")
  #|	   ((unk) "$order" "$dkummer_u")
  #|	   ((mtimes ) ((mexpt  ) x -1)
  #|	    ((mplus ) ((mtimes  ) a 
  #|			   (($kummer_u ) a b x))
  #|	     ((mtimes  ) -1 (($dkummer_u ) a b x) b)
  #|	     ((mtimes  ) (($dkummer_u ) a b x) x))))
  #|	 'grad)

///|
fn init_share_kummer() -> Unit raise {
  share_odeutils__eval_put_forms(share_kummer__forms)
}
