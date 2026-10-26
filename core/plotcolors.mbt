// Port of src/plotcolors.lisp: functions to manage colors in plot2d/plot3d
// and draw2d/draw3d.
//
// The following notations are used for colors:
// 1. A list of red, green and blue, being all numbers between 0 and 1.
// 2. A string "#rrggbb", where rr, gg and bb are 2-digit hexadecimal numbers
//    (the red, green and blue components).
// 3. A symbol whose name is one of the 139 color names accepted in HTML/CSS.
// 4. A string that after removal of any white spaces, hyphens and
//    underscores is one of the color names accepted in HTML/CSS.
//
// Helpers shared by the colour code below, by plot.lisp and by the graphics
// drivers live here because this file is the lowest layer of the plotting
// stack.

///|
fn ensure_string(x : Value) -> Value raise {
  if stringp(x) {
    x
  } else if symbolp(x) {
    print_invert_case(stripdollar(x))
  } else {
    maybe_invert_string_case(string(implode(strgrind(x))))
  }
}

///|
fn coerce_float(x : Value) -> Value raise {
  d_float(meval(x))
}

///|
/// Test for real numbers between 0 and 1
fn real01p(x : Value) -> Value raise {
  lbool(realp(x) && num_ge(x, Fix(0L)) && num_le(x, Fix(1L)))
}

///|
/// Down-case a string, removing spaces, minus signs, and underscores.  It
/// is used to allow valid color names to be written as DarkBlue, dark_blue
/// or 'Dark blue', all meaning darkblue.
fn atom_to_downcased_string(val : Value) -> Value raise {
  let s = string_downcase(string_trim("\"", char_list_to_string(mstring(val))))
  let sb = StringBuilder::new()
  for c in s {
    let n = c.to_int()
    if n != 32 && n != 45 && n != 95 {
      sb.write_char(c)
    }
  }
  Str(sb.to_string())
}

///|
/// The 139 colors names accepted in Maxima plots (the same color names
/// accepted in HTML and CSS): the initial contents of *COLOR-TABLE*.
let plotcolors__table : Array[(String, String)] = [
  ("aliceblue", "#f0f8ff"),
  ("antiquewhite", "#faebd7"),
  ("aqua", "#00ffff"),
  ("aquamarine", "#7fffd4"),
  ("azure", "#f0ffff"),
  ("beige", "#f5f5dc"),
  ("bisque", "#ffe4c4"),
  ("black", "#000000"),
  ("blanchedalmond", "#ffebcd"),
  ("blue", "#0000ff"),
  ("blueviolet", "#8a2be2"),
  ("brown", "#a52a2a"),
  ("burlywood", "#deb887"),
  ("cadetblue", "#5f9ea0"),
  ("chartreuse", "#7fff00"),
  ("chocolate", "#d2691e"),
  ("coral", "#ff7f50"),
  ("cornflowerblue", "#6495ed"),
  ("cornsilk", "#fff8dc"),
  ("crimson", "#dc143c"),
  ("cyan", "#00ffff"),
  ("darkblue", "#00008b"),
  ("darkcyan", "#008b8b"),
  ("darkgoldenrod", "#b8860b"),
  ("darkgray", "#a9a9a9"),
  ("darkgrey", "#a9a9a9"),
  ("darkgreen", "#006400"),
  ("darkkhaki", "#bdb76b"),
  ("darkmagenta", "#8b008b"),
  ("darkolivegreen", "#556b2f"),
  ("darkorange", "#ff8c00"),
  ("darkorchid", "#9932cc"),
  ("darkred", "#8b0000"),
  ("darksalmon", "#e9967a"),
  ("darkseagreen", "#8fbc8f"),
  ("darkslateblue", "#483d8b"),
  ("darkslategray", "#2f4f4f"),
  ("darkslategrey", "#2f4f4f"),
  ("darkturquoise", "#00ced1"),
  ("darkviolet", "#9400d3"),
  ("deeppink", "#ff1493"),
  ("deepskyblue", "#00bfff"),
  ("dimgray", "#696969"),
  ("dimgrey", "#696969"),
  ("dodgerblue", "#1e90ff"),
  ("firebrick", "#b22222"),
  ("floralwhite", "#fffaf0"),
  ("forestgreen", "#228b22"),
  ("fuchsia", "#ff00ff"),
  ("gainsboro", "#dcdcdc"),
  ("ghostwhite", "#f8f8ff"),
  ("gold", "#ffd700"),
  ("goldenrod", "#daa520"),
  ("gray", "#bebebe"),
  ("grey", "#bebebe"),
  ("green", "#00ff00"),
  ("greenyellow", "#adff2f"),
  ("honeydew", "#f0fff0"),
  ("hotpink", "#ff69b4"),
  ("indianred", "#cd5c5c"),
  ("indigo", "#4b0082"),
  ("ivory", "#fffff0"),
  ("khaki", "#f0e68c"),
  ("lavender", "#e6e6fa"),
  ("lavenderblush", "#fff0f5"),
  ("lawngreen", "#7cfc00"),
  ("lemonchiffon", "#fffacd"),
  ("lightblue", "#add8e6"),
  ("lightcoral", "#f08080"),
  ("lightcyan", "#e0ffff"),
  ("lightgoldenrodyellow", "#fafad2"),
  ("lightgray", "#d3d3d3"),
  ("lightgrey", "#d3d3d3"),
  ("lightgreen", "#90ee90"),
  ("lightpink", "#ffb6c1"),
  ("lightsalmon", "#ffa07a"),
  ("lightseagreen", "#20b2aa"),
  ("lightskyblue", "#87cefa"),
  ("lightslategray", "#778899"),
  ("lightslategrey", "#778899"),
  ("lightsteelblue", "#b0c4de"),
  ("lightyellow", "#ffffe0"),
  ("lime", "#00ff00"),
  ("limegreen", "#32cd32"),
  ("linen", "#faf0e6"),
  ("magenta", "#ff00ff"),
  ("maroon", "#b03060"),
  ("mediumaquamarine", "#66cdaa"),
  ("mediumblue", "#0000cd"),
  ("mediumorchid", "#ba55d3"),
  ("mediumpurple", "#9370db"),
  ("mediumseagreen", "#3cb371"),
  ("mediumslateblue", "#7b68ee"),
  ("mediumspringgreen", "#00fa9a"),
  ("mediumturquoise", "#48d1cc"),
  ("mediumvioletred", "#c71585"),
  ("midnightblue", "#191970"),
  ("mintcream", "#f5fffa"),
  ("mistyrose", "#ffe4e1"),
  ("moccasin", "#ffe4b5"),
  ("navajowhite", "#ffdead"),
  ("navy", "#000080"),
  ("oldlace", "#fdf5e6"),
  ("olive", "#808000"),
  ("olivedrab", "#6b8e23"),
  ("orange", "#ffa500"),
  ("orangered", "#ff4500"),
  ("orchid", "#da70d6"),
  ("palegoldenrod", "#eee8aa"),
  ("palegreen", "#98fb98"),
  ("paleturquoise", "#afeeee"),
  ("palevioletred", "#db7093"),
  ("papayawhip", "#ffefd5"),
  ("peachpuff", "#ffdab9"),
  ("peru", "#cd853f"),
  ("pink", "#ffc0cb"),
  ("plum", "#dda0dd"),
  ("powderblue", "#b0e0e6"),
  ("purple", "#a020f0"),
  ("rebeccapurple", "#663399"),
  ("red", "#ff0000"),
  ("rosybrown", "#bc8f8f"),
  ("royalblue", "#4169e1"),
  ("saddlebrown", "#8b4513"),
  ("salmon", "#fa8072"),
  ("sandybrown", "#f4a460"),
  ("seagreen", "#2e8b57"),
  ("seashell", "#fff5ee"),
  ("sienna", "#a0522d"),
  ("silver", "#c0c0c0"),
  ("skyblue", "#87ceeb"),
  ("slateblue", "#6a5acd"),
  ("slategray", "#708090"),
  ("slategrey", "#708090"),
  ("snow", "#fffafa"),
  ("springgreen", "#00ff7f"),
  ("steelblue", "#4682b4"),
  ("tan", "#d2b48c"),
  ("teal", "#008080"),
  ("thistle", "#d8bfd8"),
  ("tomato", "#ff6347"),
  ("turquoise", "#40e0d0"),
  ("violet", "#ee82ee"),
  ("wheat", "#f5deb3"),
  ("white", "#ffffff"),
  ("whitesmoke", "#f5f5f5"),
  ("yellow", "#ffff00"),
  ("yellowgreen", "#9acd32"),
]

///|
/// (and (string= (subseq color 0 1) "#") (= (length color) 7)
///      (ignore-errors (parse-integer (subseq color 1 6) :radix 16)))
fn plotcolors__hex_color_p(color : String) -> Bool raise {
  if string_length(color) < 1 {
    // (subseq color 0 1) signals an error on an empty string
    raise LispError::SimpleError(
      "The bounding indices 0 and 1 are bad for a sequence of length 0.",
    )
  }
  lstring(subseq(Str(color), 0, end=1)) == "#" &&
  string_length(color) == 7 &&
  parse_integer(lstring(subseq(Str(color), 1, end=6)), radix=16) is Some(_)
}

///|
/// Returns true if the given symbol or string is a valid plot color;
/// namely, a color name among the predefined colors or a six-digit
/// hexadecimal number with a # suffix.  The color names can be in upper or
/// lower case (or a mix of both) and with any spaces, hyphens or
/// underscores.
fn plotcolorp(clr : Value) -> Value raise {
  let color = lstring(atom_to_downcased_string(ensure_string(clr)))
  if plotcolors__hex_color_p(color) {
    t
  } else if gethash2(Str(color), symval(q_ear_color_table)).1 {
    t
  } else {
    Nil
  }
}

///|
/// (parse-integer s :radix 16), signalling an error on junk.
fn plotcolors__parse_hex(s : String) -> Value raise {
  match parse_integer(s, radix=16) {
    Some(v) => v
    None =>
      raise LispError::SimpleError(
        "junk in string \"" + s + "\"",
      )
  }
}

///|
/// Given a color in the #rrggbb notation, returns a list with red, green
/// and blue values between 0.0 and 1.0
fn hex_to_numeric_list(str : Value) -> Value raise {
  let comp = (i : Int) => num_div(
    plotcolors__parse_hex(lstring(subseq(str, i, end=i + 2))),
    Flo(255.0),
  )
  let r = comp(1)
  let g = comp(3)
  let b = comp(5)
  list3(r, g, b)
}

///|
/// Transform a list with three components between 0.0 and 1.0 (red, green
/// and blue components) into a color code #rrggbb
fn numeric_list_to_rgb(c : Value) -> Value raise {
  if length(c) == 3 {
    Str(
      string_downcase(
        lstring(
          format(Nil, "#~{~16,2,'0R~}", [
            mapcar(x => round1(num_mul(Fix(255L), x)), c),
          ]),
        ),
      ),
    )
  } else {
    Str("#000000")
  }
}

///|
/// Find the RGB color code #rrggbb for a given symbol or string that
/// represents one of the predefined colors. Returns nil if the color is not
/// in the predefined colors list.
fn rgb_color(clr : Value) -> Value raise {
  let color = lstring(atom_to_downcased_string(ensure_string(clr)))
  if plotcolors__hex_color_p(color) {
    return Str(color)
  }
  let code = gethash(Str(color), symval(q_ear_color_table))
  if code.truthy() {
    code
  } else {
    Nil
  }
}

///|
/// (mapcar fn l1 l2)
fn plotcolors__map2(
  f : (Value, Value) -> Value raise,
  l1 : Value,
  l2 : Value,
) -> Value raise {
  let acc = Collector::new()
  let mut a = l1
  let mut b = l2
  while a is Cons(_) && b is Cons(_) {
    acc.add(f(car(a), car(b)))
    a = cdr(a)
    b = cdr(b)
  }
  acc.result()
}

///|
/// Interpolate between two or more colors, given as strings #rrggbb,
/// according to a fraction f, between 0 and 1, where 0 gives the first
/// color and 1 the last one.
fn interpolate_color(
  f : Value,
  rgb1 : Value,
  rgb2 : Value,
  rgb : Value,
) -> Value raise {
  let colors = cons(rgb1, cons(rgb2, rgb))
  let l = length(colors)
  let (n, r) = num_floor(num_mul(f, int(l - 1)))
  if num_eq(n, int(l - 1)) {
    last(colors)
  } else {
    let c1 = hex_to_numeric_list(nth(to_int(n), colors))
    let c2 = hex_to_numeric_list(nth(to_int(n) + 1, colors))
    numeric_list_to_rgb(
      plotcolors__map2(
        (a, b) => num_add(a, b),
        c1,
        mapcar(
          x => num_mul(r, x),
          plotcolors__map2((a, b) => num_sub(a, b), c2, c1),
        ),
      ),
    )
  }
}

///|
/// Convert a color given as HSV (hue, saturation, value), all between 0 and
/// 1, to RGB as a string #rrggbb.
fn d_hsv(hue : Value, sat : Value, val : Value) -> Value raise {
  let h = coerce_float(hue)
  let s = coerce_float(sat)
  let v = coerce_float(val)
  if !(real01p(h).truthy() && real01p(s).truthy() && real01p(v).truthy()) {
    merr("The arguments of hsv must be between 0 and 1.~%", []) |> ignore
  }
  if zerop(s) {
    // Achromatic case (gray)
    numeric_list_to_rgb(list3(v, v, v))
  } else {
    let (i, f) = num_floor(num_mul(h, Fix(6L)))
    let p = num_mul(v, num_sub(Fix(1L), s))
    let q = num_mul(v, num_sub(Fix(1L), num_mul(s, f)))
    let tt = num_mul(v, num_sub(Fix(1L), num_mul(s, num_sub(Fix(1L), f))))
    let rgb = match to_int(i) {
      0 | 6 => list3(v, tt, p)
      1 => list3(q, v, p)
      2 => list3(p, v, tt)
      3 => list3(p, q, v)
      4 => list3(tt, p, v)
      5 => list3(v, p, q)
      _ => Nil
    }
    numeric_list_to_rgb(rgb)
  }
}

///|
fn init_plotcolors() -> Unit raise {
  // (defvar *color-table* (make-hash-table :test 'equal)), then populated
  let tab = make_hash_table(kind=Equal)
  for kv in plotcolors__table {
    sethash(Str(kv.0), tab, Str(kv.1)) |> ignore
  }
  set(q_ear_color_table, tab) |> ignore
}
