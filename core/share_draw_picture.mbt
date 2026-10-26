// Port of share/draw/picture.lisp: the picture package (level, rgb and
// rgb_alpha pictures) and the XPM image reader.

///|
/// Top-level forms of picture.lisp: only (defvar *xpm-readtable* nil),
/// whose literal value gen_vars.mbt sets.
fn init_share_picture() -> Unit raise {

}

///|
fn cut_and_round(seq : Value) -> Value raise {
  mapcar(
    z => {
      let fz = meval(list2(list1(q_d_float), z))
      if num_lt(fz, Fix(0L)) {
        Fix(0L)
      } else if num_gt(fz, Fix(255L)) {
        Fix(255L)
      } else {
        round1(fz)
      }
    },
    seq,
  )
}

///|
/// Constructs a levels picture. This object contains four parts:
/// 1) symbol 'level
/// 2) image width
/// 3) image height
/// 4) an integer array with pixel data ranging from 0 to 255.
/// Argument data must contain only numbers ranged from 0 to 255; negative
/// numbers are substituted by 0, and those which are greater than 255 are
/// set to 255. If data is a Maxima list, width and height must be given.
fn d_make_level_picture(
  data : Value,
  wi? : Value = Nil,
  he? : Value = Nil,
) -> Value raise {
  let mut width : Value = Nil
  let mut height : Value = Nil
  let mut picarray : Value = Nil
  if d_matrixp(data).truthy() {
    width = int(length(cdadr(data)))
    height = int(length(cdr(data)))
    picarray = vector(
      list_to_array(cut_and_round(rest(d_flatten(d_args(data))))),
    )
  } else if d_listp(data).truthy() &&
    integerp(wi) &&
    integerp(he) &&
    num_eq(num_mul(wi, he), d_length(data)) {
    width = wi
    height = he
    picarray = vector(list_to_array(cut_and_round(rest(data))))
  } else {
    merr(
      "make_level_picture: argument must be a matrix, or a list of integers with length = width*height.",
      [],
    )
    |> ignore
  }
  list([list1(q_d_picture), q_d_level, width, height, picarray])
}

///|
/// The elements of a vector.
fn share_draw_picture__data(v : Value) -> Array[Value] raise {
  match v {
    Vec(a) =>
      match a.fill {
        Some(f) => a.data[0:f].to_array()
        None => a.data
      }
    _ => raise LispError::SimpleError("not a vector: " + princ_to_string(v))
  }
}

///|
/// Returns true if the argument is a well formed image, and false
/// otherwise.
fn d_picturep(x : Value) -> Value raise {
  if !(
      consp(x) &&
      eq(caar(x), q_d_picture) &&
      length(x) == 5 &&
      memq(second(x), list([q_d_level, q_d_rgb, q_d_rgb_alpha])).truthy() &&
      integerp(third(x)) &&
      integerp(fourth(x)) &&
      vectorp(fifth(x))
    ) {
    return Nil
  }
  let n = share_draw_picture__data(fifth(x)).length()
  let wh = num_mul(third(x), fourth(x))
  let ok = if eq(second(x), q_d_level) {
    num_eq(int(n), wh)
  } else if eq(second(x), q_d_rgb) {
    num_eq(int(n), num_mul(Fix(3L), wh))
  } else {
    num_eq(int(n), num_mul(Fix(4L), wh))
  }
  if !ok {
    return Nil
  }
  for z in share_draw_picture__data(fifth(x)) {
    if !(integerp(z) && num_ge(z, Fix(0L)) && num_le(z, Fix(255L))) {
      return Nil
    }
  }
  t
}

///|
/// Returns true in case of equal pictures, and false otherwise.
fn d_picture_equalp(pic1 : Value, pic2 : Value) -> Value raise {
  if d_picturep(pic1).truthy() && d_picturep(pic2).truthy() {
    alike1(pic1, pic2)
  } else {
    merr("picture_equalp: both arguments must be picture objects.", [])
  }
}

///|
/// Constructs a coloured rgb picture. This object contains four parts:
/// 1) symbol 'rgb
/// 2) image width
/// 3) image height
/// 4) an integer array of length 3*width*height with pixel data ranging
///    from 0 to 255. Each pixel is represented by three consecutive
///    numbers (red, green, blue). Arguments must contain the three channels
///    in level_picture.
fn d_make_rgb_picture(
  redlevel : Value,
  greenlevel : Value,
  bluelevel : Value,
) -> Value raise {
  if !(
      d_picturep(redlevel).truthy() &&
      equal(cadr(redlevel), q_d_level) &&
      d_picturep(greenlevel).truthy() &&
      equal(cadr(greenlevel), q_d_level) &&
      d_picturep(bluelevel).truthy() &&
      equal(cadr(bluelevel), q_d_level)
    ) {
    merr(
      "make_rgb_picture: every color channel must be a picture object with type = level.",
      [],
    )
    |> ignore
  }
  if !(
      num_eq(caddr(redlevel), caddr(greenlevel)) &&
      num_eq(caddr(greenlevel), caddr(bluelevel)) &&
      num_eq(cadddr(redlevel), cadddr(greenlevel)) &&
      num_eq(cadddr(greenlevel), cadddr(bluelevel))
    ) {
    merr("make_rgb_picture: color channels are not of equal dimensions.", [])
    |> ignore
  }
  let width = caddr(redlevel)
  let height = cadddr(redlevel)
  let leng = to_int(num_mul(width, height))
  let picarray = make_array([3 * leng], elt="integer")
  for i in 0..<leng {
    let i3 = 3 * i
    aset1(picarray, i3, aref1(nth(4, redlevel), i)) |> ignore
    aset1(picarray, i3 + 1, aref1(nth(4, greenlevel), i)) |> ignore
    aset1(picarray, i3 + 2, aref1(nth(4, bluelevel), i)) |> ignore
  }
  list([list1(q_d_picture), q_d_rgb, width, height, picarray])
}

///|
/// Extracts color channel ('red, 'green or 'blue) from a coloured picture.
/// Returns a levels picture.
fn d_take_channel(pic : Value, chn : Value) -> Value raise {
  if !(
      d_picturep(pic).truthy() &&
      (equal(cadr(pic), q_d_rgb) || equal(cadr(pic), q_d_rgb_alpha))
    ) {
    merr(
      "take_channel: first argument must be a picture object with type = rgb or rgb_alpha.",
      [],
    )
    |> ignore
  }
  if !member(chn, list([q_d_red, q_d_green, q_d_blue])).truthy() {
    merr("take_channel: color channel must be red, green, or blue.", [])
    |> ignore
  }
  let width = caddr(pic)
  let height = cadddr(pic)
  let dim = to_int(num_mul(width, height))
  let img = make_array([dim], elt="integer")
  let stride = if eq(second(pic), q_d_rgb) { 3 } else { 4 }
  let idx = if eq(chn, q_d_red) {
    0
  } else if eq(chn, q_d_green) {
    1
  } else {
    2
  }
  for i in 0..<dim {
    aset1(img, i, aref1(nth(4, pic), stride * i + idx)) |> ignore
  }
  list([list1(q_d_picture), q_d_level, width, height, img])
}

///|
/// Returns the negative of a (level or rgb) picture. For RGB images with
/// alpha channel, take the negative of RGB channels, and return alpha
/// channel unmodified.
fn d_negative_picture(pic : Value) -> Value raise {
  if !d_picturep(pic).truthy() {
    merr("negative_picture: argument must be a picture object.", []) |> ignore
  }
  let dim = array_dimension(nth(4, pic), 0)
  let stride = if eq(second(pic), q_d_rgb) {
    3
  } else if eq(second(pic), q_d_level) {
    1
  } else {
    4
  }
  let arr = copy_seq(nth(4, pic))
  let neg = (k : Int) => aset1(arr, k, num_sub(Fix(255L), aref1(arr, k)))
    |> ignore
  for i in 0..<(dim / stride) {
    let base = i * stride
    if eq(second(pic), q_d_level) {
      neg(base)
    } else {
      neg(base)
      neg(base + 1)
      neg(base + 2)
    }
  }
  list([list1(q_d_picture), nth(1, pic), nth(2, pic), nth(3, pic), arr])
}

///|
/// Transforms an rgb picture into a level one by averaging the red, green
/// and blue values. The alpha channel, if present, is ignored.
fn d_rgb2level(pic : Value) -> Value raise {
  if !d_picturep(pic).truthy() ||
    !(equal(nth(1, pic), q_d_rgb) || equal(nth(1, pic), q_d_rgb_alpha)) {
    merr(
      "rgb2level: argument must be a picture object with type = rgb or rgb_alpha.",
      [],
    )
    |> ignore
  }
  let level_dim = to_int(num_mul(nth(2, pic), nth(3, pic)))
  let rgb_stride = if eq(nth(1, pic), q_d_rgb) { 3 } else { 4 }
  let rgb_array = nth(4, pic)
  let level_array = make_array([level_dim], elt="integer")
  for i in 0..<level_dim {
    let rgb_base = rgb_stride * i
    aset1(
      level_array,
      i,
      round1(
        num_div(
          num_sum([
            aref1(rgb_array, rgb_base),
            aref1(rgb_array, rgb_base + 1),
            aref1(rgb_array, rgb_base + 2),
          ]),
          Fix(3L),
        ),
      ),
    )
    |> ignore
  }
  list([list1(q_d_picture), q_d_level, nth(2, pic), nth(3, pic), level_array])
}

///|
/// Returns pixel from picture. Coordinates x and y range from 0 to
/// (width-1) and (height-1), respectively. For RGB pictures, return a list
/// of 3 elements, R, G, and B. For RGB + alpha pictures, return a list of 4
/// elements, R, G, B, and alpha.
fn d_get_pixel(pic : Value, x : Value, y : Value) -> Value raise {
  if !d_picturep(pic).truthy() {
    merr("get_pixel: first argument must be a picture object.", []) |> ignore
  }
  if !(integerp(x) && integerp(y)) {
    merr("get_pixel: pixel coordinates must be integers.", []) |> ignore
  }
  if !(
      num_gt(x, Fix(-1L)) &&
      num_lt(x, nth(2, pic)) &&
      num_gt(y, Fix(-1L)) &&
      num_lt(y, nth(3, pic))
    ) {
    merr("get_pixel: pixel coordinates out of range.", []) |> ignore
  }
  let stride = if eq(second(pic), q_d_rgb) {
    3
  } else if eq(second(pic), q_d_level) {
    1
  } else {
    4
  }
  let data = nth(4, pic)
  let kind = nth(1, pic)
  let idx = to_int(num_add(x, num_mul(y, nth(2, pic))))
  if eq(kind, q_d_level) {
    aref1(data, idx)
  } else if eq(kind, q_d_rgb) {
    let pos = stride * idx
    list([
      list1(q_mlist),
      aref1(data, pos),
      aref1(data, pos + 1),
      aref1(data, pos + 2),
    ])
  } else if eq(kind, q_d_rgb_alpha) {
    let pos = stride * idx
    list([
      list1(q_mlist),
      aref1(data, pos),
      aref1(data, pos + 1),
      aref1(data, pos + 2),
      aref1(data, pos + 3),
    ])
  } else {
    Nil
  }
}

// ---------------------------------------------------------------------------
// XPM IMAGE FORMAT SUPPORT
//
// The following functions have been taken from
// http://common-lisp.net/project/gamelib/ (MIT license). They read the
// image with the CL reader and a readtable in which / starts a C comment
// (ended by */) and the comma is whitespace; the port emulates that
// reader on the few token kinds that occur in XPM files: strings, numbers
// and symbols.

///|
/// Sets up *xpm-readtable* (the port's reader for XPM files needs no
/// table; the variable only records that it has been initialized).
fn init_readtable() -> Value raise {
  if !symval(q_ear_xpm_readtable).truthy() {
    set(q_ear_xpm_readtable, t) |> ignore
  }
  Nil
}

///|
fn skip_whitespace(f : Value) -> Value raise {
  while true {
    let c = read_char(stream=f, eof_value=Nil)
    match c {
      Char(' ') | Char('\t') => continue
      Char(ch) => {
        unread_char(ch, stream=f)
        break
      }
      _ => break
    }
  }
  Nil
}

///|
fn extract_r_g_b_bits(
  n__bits_per_color_output : Value,
  n__hex_digits_input : Value,
  value : Value,
) -> Value raise {
  let n_in = num_ceiling(num_div(num_mul(n__hex_digits_input, Fix(4L)), Fix(3L))).0
  let n_out = n__bits_per_color_output
  let nin = to_int(n_in)
  let shift = to_int(num_sub(n_out, n_in))
  let r_in = ash(value, -(nin * 2))
  let g_in = num_mod(ash(value, -nin), ash(Fix(1L), nin))
  let b_in = num_mod(value, ash(Fix(1L), nin))
  list([ash(r_in, shift), ash(g_in, shift), ash(b_in, shift)])
}

///|
/// A character of the XPM reader's whitespace (comma included).
fn share_draw_picture__whitespace(c : Char) -> Bool {
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == ',' || c == '\x0c'
}

///|
/// Skips a C comment after its initial /, as nparse.lisp's GOBBLE-COMMENT.
fn share_draw_picture__gobble_comment(f : Value) -> Unit raise {
  let mut depth = 1
  while true {
    let c = read_char(stream=f, eof_value=Nil)
    match c {
      Char('*') =>
        if peek_char(stream=f, eof_value=Nil) is Char('/') {
          depth = depth - 1
          read_char(stream=f) |> ignore
          if depth == 0 {
            return
          }
        }
      Char('/') =>
        if peek_char(stream=f, eof_value=Nil) is Char('*') {
          depth = depth + 1
          read_char(stream=f) |> ignore
        }
      Char(_) => ()
      _ => {
        merr("end of file in comment.", []) |> ignore
        return
      }
    }
  }
}

///|
/// (read f eof-error-p eof-value) with the XPM readtable: a string, an
/// integer or a symbol (an interned symbol named by the upcased token).
fn share_draw_picture__read(
  f : Value,
  eof_error? : Bool = true,
  eof_value? : Value = Nil,
) -> Value raise {
  // skip whitespace and comments
  let mut first : Char = ' '
  while true {
    match read_char(stream=f, eof_value=Nil) {
      Char(c) =>
        if share_draw_picture__whitespace(c) {
          continue
        } else if c == '/' {
          share_draw_picture__gobble_comment(f)
        } else if c == ';' {
          // comment to the end of the line
          while true {
            match read_char(stream=f, eof_value=Nil) {
              Char('\n') => break
              Char(_) => continue
              _ => break
            }
          }
        } else {
          first = c
          break
        }
      _ =>
        if eof_error {
          raise LispError::Condition(
            intern("end-of-file"),
            "end of file on stream",
            f,
          )
        } else {
          return eof_value
        }
    }
  }
  if first == '"' {
    let sb = StringBuilder::new()
    while true {
      match read_char(stream=f, eof_value=Nil) {
        Char('"') => break
        Char('\\') =>
          match read_char(stream=f, eof_value=Nil) {
            Char(c) => sb.write_char(c)
            _ =>
              raise LispError::Condition(
                intern("end-of-file"),
                "end of file on stream",
                f,
              )
          }
        Char(c) => sb.write_char(c)
        _ =>
          raise LispError::Condition(
            intern("end-of-file"),
            "end of file on stream",
            f,
          )
      }
    }
    return Str(sb.to_string())
  }
  let sb = StringBuilder::new()
  sb.write_char(first)
  while true {
    match read_char(stream=f, eof_value=Nil) {
      Char(c) =>
        if share_draw_picture__whitespace(c) ||
          c == '"' ||
          c == ';' ||
          c == '(' ||
          c == ')' ||
          c == '\'' ||
          c == '`' {
          unread_char(c, stream=f)
          break
        } else {
          sb.write_char(c)
        }
      _ => break
    }
  }
  let tok = sb.to_string()
  match parse_integer(tok) {
    Some(n) => n
    None => sym(tok.to_upper())
  }
}

///|
/// Returns a list of two elements comprising rgb bits and alpha.
fn read_colour(f : Value) -> Value raise {
  let ctype = read_char(stream=f)
  match ctype {
    Char('#') => {
      // We have encountered an RGB color in hexadecimal format. Return a
      // list of two elements comprising packed rgb bits and alpha = 255
      // (fully opaque color).
      let sb = StringBuilder::new()
      let mut ndigits = 0
      while true {
        match read_char(stream=f, eof_value=Nil) {
          Char(c) =>
            if digit_char_p(c, radix=16) is Some(_) {
              sb.write_char(c)
              ndigits = ndigits + 1
            } else {
              unread_char(c, stream=f)
              break
            }
          _ => break
        }
      }
      let value = match parse_integer(sb.to_string(), radix=16) {
        Some(v) => v
        None =>
          raise LispError::SimpleError(
            "parse-integer: no digits in \"" + sb.to_string() + "\"",
          )
      }
      // Some XPM images contain 12 hex digits per color; truncate colors
      // to 8 bits (i.e., 2 hex digits per color, 6 hex digits in all).
      list2(extract_r_g_b_bits(Fix(8L), int(ndigits), value), Fix(255L))
    }
    _ => {
      // color name:
      // 0. read the rest of the name and append the first letter
      // 1. get the hexadecimal code from *color-table* defined in
      //    grcommon.lisp
      // 2. remove # and transform the code to an integer in base 10
      let color_name = share_draw__atom_to_downcased_string(
        format(Nil, "~a~a", [ctype, share_draw_picture__read(f)]),
      )
      let mut alpha = 0
      let mut color_bits : Value = Fix(0L)
      if color_name == "none" {
        alpha = 0
        color_bits = Fix(0L)
      } else {
        let color_table_value = share_draw__color_table_get(color_name)
        alpha = 255
        if color_table_value is Nil {
          merr("read_xpm: unrecognized color name ~M", [Str(color_name)])
          |> ignore
        } else {
          let s = lstring(color_table_value)
          color_bits = match parse_integer(s.view(start_offset=1).to_string(), radix=16) {
            Some(v) => v
            None => raise LispError::SimpleError("parse-integer: junk in " + s)
          }
        }
      }
      // Assume all color table items are 6 hex digits.
      list2(extract_r_g_b_bits(Fix(8L), Fix(6L), color_bits), int(alpha))
    }
  }
}

///|
fn read_charspec(f : Value, cnt : Value) -> Value raise {
  let sb = StringBuilder::new()
  for _ in 0..<to_int(cnt) {
    match read_char(stream=f, eof_value=Nil) {
      Char(c) => sb.write_char(c)
      _ =>
        raise LispError::Condition(
          intern("end-of-file"),
          "end of file on stream",
          f,
        )
    }
  }
  Str(sb.to_string())
}

///|
fn read_color_spec_for_type(
  str : Value,
  cnt : Value,
  hash : Value,
  type_char : Value,
) -> Value raise {
  let cs = make_string_input_stream(lstring(str))
  let chars = read_charspec(cs, cnt)
  skip_whitespace(cs) |> ignore
  let mut c = read_char(stream=cs, eof_value=Nil)
  if c is Nil {
    raise LispError::Condition(
      intern("end-of-file"),
      "end of file on stream",
      cs,
    )
  }
  while c.truthy() && !eql(c, type_char) {
    share_draw_picture__read(cs, eof_error=false) |> ignore
    skip_whitespace(cs) |> ignore
    c = read_char(stream=cs, eof_value=Nil)
  }
  if c.truthy() && eql(c, type_char) {
    let color_spec = {
      skip_whitespace(cs) |> ignore
      read_colour(cs)
    }
    sethash(chars, hash, color_spec)
  } else {
    Nil
  }
}

///|
fn read_color_spec(str : Value, cnt : Value, hash : Value) -> Value raise {
  let a = read_color_spec_for_type(str, cnt, hash, Char('c'))
  if a.truthy() {
    return a
  }
  let b = read_color_spec_for_type(str, cnt, hash, Char('m'))
  if b.truthy() {
    return b
  }
  let g = read_color_spec_for_type(str, cnt, hash, Char('g'))
  if g.truthy() {
    return g
  }
  merr("read_xpm: failed to parse color specification ''~M''", [str])
}

///|
fn d_read_xpm(mfspec : Value) -> Value raise {
  if streamp(mfspec) {
    read_xpm_from_stream(mfspec)
  } else {
    let fspec = string_trim("\"", char_list_to_string(mstring(mfspec)))
    let image = open_input_file(fspec)
    read_xpm_from_stream(image)
  }
}

///|
fn read_xpm_from_stream(image : Value) -> Value raise {
  init_readtable() |> ignore
  // (ignore-errors (read-line image))
  let first_line_raw = read_line(stream=image)
  match first_line_raw {
    Some(raw) => {
      let first_line = string_trim(" \t\r\n", raw)
      if first_line != "/* XPM */" {
        if first_line == "! XPM2" {
          merr("read_xpm: I don't know how to read XPM2 format.", []) |> ignore
        } else {
          merr(
            "read_xpm: input doesn't appear to be XPM3 format; first line: ~M",
            [Str(first_line)],
          )
          |> ignore
        }
      }
    }
    _ =>
      merr(
        "read_xpm: failed to read first line; are you sure this is an XPM image?",
        [],
      )
      |> ignore
  }
  // Burn off any additional comment or comments, and C code ending in left
  // curly brace.
  while true {
    let x = share_draw_picture__read(image)
    if eq(x, sym("{")) {
      break
    }
  }
  let colspec = share_draw_picture__read(image)
  let chartab = make_hash_table(kind=Equal)
  let cspec = make_string_input_stream(lstring(colspec))
  let width = share_draw_picture__read(cspec)
  let height = share_draw_picture__read(cspec)
  let colours = share_draw_picture__read(cspec)
  let cpp = share_draw_picture__read(cspec)
  let mut counter = -1
  for _cix in 0..<to_int(colours) {
    let c = share_draw_picture__read(image)
    read_color_spec(c, cpp, chartab) |> ignore
  }
  let w = to_int(width)
  let h = to_int(height)
  let img = make_array([4 * w * h], elt="integer")
  for y in 0..<h {
    let line = share_draw_picture__read(image)
    if !stringp(line) {
      merr("read_xpm: failed to read ~M'th line of image; found: ~M", [
        int(y + 1),
        line,
      ])
      |> ignore
    }
    let data = make_string_input_stream(lstring(line))
    for _x in 0..<w {
      let cs = read_charspec(data, cpp)
      let rgb_alpha = gethash(cs, chartab)
      let rgb = first(rgb_alpha)
      let alpha = second(rgb_alpha)
      counter = counter + 1
      aset1(img, counter, first(rgb)) |> ignore
      counter = counter + 1
      aset1(img, counter, second(rgb)) |> ignore
      counter = counter + 1
      aset1(img, counter, third(rgb)) |> ignore
      counter = counter + 1
      aset1(img, counter, alpha) |> ignore
    }
  }
  list([list1(q_d_picture), q_d_rgb_alpha, width, height, img])
}
