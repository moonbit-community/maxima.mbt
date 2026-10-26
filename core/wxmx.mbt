// Port of src/wxmx.lisp: reading the Maxima input out of a wxMaxima .wxmx
// worksheet.
//
// A .wxmx file is a .zip container whose member content.xml holds the
// whole worksheet: text cells, input cells and the output wxMaxima last
// displayed.  wxMaxima writes the mimetype, format.txt and content.xml
// members uncompressed and ahead of the images, so the input cells can be
// recovered by walking the local file headers of the archive -- no
// decompressor and no complete .zip reader needed.  A member that is
// compressed, or that defers its size to a data descriptor, is diagnosed
// rather than guessed at.
//
// The port's runtime has no binary file streams: the (unsigned-byte 8)
// input stream WITH-OPEN-FILE gives WXMX-INPUT-STRING is a
// "wxmx-octet-stream" structure holding the file's octets and a position.
// Octet vectors are Lisp vectors of fixnums, and the adjustable strings
// the text is pushed onto are character vectors with a fill pointer.

///|
/// The signature of a .zip local file header, "PK\3\4" read as a
/// little-endian 32 bit integer.
let wxmx__local_file_header : Int64 = 0x04034b50L

///|
/// An XML reference is short: &thisisnotareference; in a text cell must
/// not swallow the text that follows it looking for a semicolon.
let wxmx__reference_length : Int = 12

///|
/// (with-open-file (stream filename :element-type '(unsigned-byte 8)))
fn wxmx__open_octet_stream(path : String) -> Value raise {
  let data = read_file_bytes(path)
  let octets : Array[Value] = []
  for b in data {
    octets.push(Fix(b.to_int64()))
  }
  make_struct("wxmx-octet-stream", [
    Vec({ data: octets, dims: [octets.length()], fill: None, elt: "(unsigned-byte 8)" }),
    Fix(0L),
  ])
}

///|
fn wxmx__stream_data(stream : Value) -> Array[Value] raise {
  match struct_ref(stream, 0) {
    Vec(a) => a.data
    _ => []
  }
}

///|
fn wxmx__stream_pos(stream : Value) -> Int raise {
  to_int(struct_ref(stream, 1))
}

///|
fn wxmx__set_stream_pos(stream : Value, pos : Int) -> Unit raise {
  struct_set(stream, 1, int(pos)) |> ignore
}

///|
/// (read-byte stream nil nil)
fn wxmx__read_byte(stream : Value) -> Value raise {
  let data = wxmx__stream_data(stream)
  let pos = wxmx__stream_pos(stream)
  if pos < data.length() {
    wxmx__set_stream_pos(stream, pos + 1)
    data[pos]
  } else {
    Nil
  }
}

///|
/// Read a little-endian 16 bit unsigned integer.  NIL at end of file.
fn wxmx_read_u16(stream : Value) -> Value raise {
  let low = wxmx__read_byte(stream)
  let high = if low.truthy() { wxmx__read_byte(stream) } else { Nil }
  if high.truthy() {
    logior(low, ash(high, 8))
  } else {
    Nil
  }
}

///|
/// Read a little-endian 32 bit unsigned integer.  NIL at end of file.
fn wxmx_read_u32(stream : Value) -> Value raise {
  let low = wxmx_read_u16(stream)
  let high = if low.truthy() { wxmx_read_u16(stream) } else { Nil }
  if high.truthy() {
    logior(low, ash(high, 16))
  } else {
    Nil
  }
}

///|
/// Read COUNT octets.  NIL if the stream does not hold that many -- a size
/// a damaged header overstates is not to be allocated first and found out
/// about afterwards.
fn wxmx_read_octets(stream : Value, count : Value) -> Value raise {
  let data = wxmx__stream_data(stream)
  let pos = wxmx__stream_pos(stream)
  if !num_le(count, int(data.length() - pos)) {
    return Nil
  }
  let n = to_int(count)
  let octets = data[pos:pos + n].to_array()
  wxmx__set_stream_pos(stream, pos + n)
  Vec({ data: octets, dims: [n], fill: None, elt: "(unsigned-byte 8)" })
}

///|
/// Move COUNT octets forward in STREAM.
fn wxmx_skip(stream : Value, count : Value) -> Value raise {
  // (file-position stream (+ (file-position stream) count)); a position
  // past the end leaves the stream at end of file.
  let length = wxmx__stream_data(stream).length()
  let p = num_add(int(wxmx__stream_pos(stream)), count)
  wxmx__set_stream_pos(
    stream,
    if num_gt(p, int(length)) {
      length
    } else {
      to_int(p)
    },
  )
  t
}

///|
/// The octets of an octet vector.
fn wxmx__octets(octets : Value) -> Array[Int] raise {
  match octets {
    Vec(a) => a.data.map(v => to_int(v))
    _ => []
  }
}

///|
/// The name a .zip local file header stores, as a string.  Member names
/// are UTF-8 or CP437; the ones we look for are plain ASCII, where the two
/// agree.
fn wxmx_member_name(octets : Value) -> Value raise {
  let sb = StringBuilder::new()
  for b in wxmx__octets(octets) {
    sb.write_char(Int::unsafe_to_char(b))
  }
  Str(sb.to_string())
}

///|
/// Return the contents of the archive member NAME of the .zip file open on
/// STREAM as a vector of octets, or NIL if there is no such member.
/// FILENAME names the archive in error messages.
fn wxmx_stored_member(stream : Value, name : Value, filename : Value) -> Value raise {
  while true {
    let sig = wxmx_read_u32(stream)
    if !eql(sig, Fix(wxmx__local_file_header)) {
      // Either the end of the last member's data, where the central
      // directory begins, or a truncated file.  Either way there is no
      // further local file header to read.
      return Nil
    }
    wxmx_read_u16(stream) |> ignore // version needed to extract
    let flags = wxmx_read_u16(stream)
    let method_ = wxmx_read_u16(stream)
    wxmx_read_u32(stream) |> ignore // modification time and date
    wxmx_read_u32(stream) |> ignore // CRC-32
    let compressed_size = wxmx_read_u32(stream)
    wxmx_read_u32(stream) |> ignore // uncompressed size
    let name_length = wxmx_read_u16(stream)
    let extra_length = wxmx_read_u16(stream)
    let member = if extra_length.truthy() {
      wxmx_read_octets(stream, name_length)
    } else {
      Nil
    }
    if member is Nil {
      return Nil
    }
    wxmx_skip(stream, extra_length) |> ignore
    // Bit 3 of the flags moves the sizes behind the member's data, into a
    // data descriptor, and leaves zeroes here.  Then there is nothing to
    // skip the member by.
    let flag3 = logbitp(3, flags)
    if lstring(name) == lstring(wxmx_member_name(member)) {
      if !eql(method_, Fix(0L)) {
        merr(
          "Cannot read the .wxmx worksheet ~A: its ~A is stored compressed, which needs a .zip decompressor.",
          [filename, name],
        )
        |> ignore
      } else if flag3 {
        merr(
          "Cannot read the .wxmx worksheet ~A: its ~A does not record its size, which needs a full .zip reader.",
          [filename, name],
        )
        |> ignore
      } else {
        return wxmx_read_octets(stream, compressed_size)
      }
    } else if flag3 {
      merr(
        "Cannot read the .wxmx worksheet ~A: the member ~A ahead of ~A does not record its size, which needs a full .zip reader.",
        [filename, wxmx_member_name(member), name],
      )
      |> ignore
    } else {
      wxmx_skip(stream, compressed_size) |> ignore
    }
  }
  Nil
}

///|
/// Whether code point CODE is a character (CHAR-CODE-LIMIT, and no
/// surrogates, as in SBCL).
fn wxmx__char_code_p(c : Int) -> Bool {
  c >= 0 && c < 0x110000 && !(c >= 0xd800 && c < 0xe000)
}

///|
/// The character of code point CODE, or a question mark where this Lisp
/// has none.
fn wxmx_code_char(code : Value) -> Value raise {
  match code {
    Fix(c) if c >= 0L && c < 0x110000L && wxmx__char_code_p(c.to_int()) =>
      Char(Int::unsafe_to_char(c.to_int()))
    _ => Char('?')
  }
}

///|
/// Decode OCTETS, a UTF-8 encoded archive member, into a string.  A
/// malformed sequence, and a character this Lisp has no CODE-CHAR for,
/// become a question mark.
fn wxmx_utf_8_string(octets : Value) -> Value raise {
  let octets = wxmx__octets(octets)
  let length = octets.length()
  let sb = StringBuilder::new()
  let mut i = 0
  while i < length {
    let byte = octets[i]
    // How many continuation bytes the leading byte promises; -1 marks a
    // byte that cannot lead one.
    let continuations = if byte < 0x80 {
      0
    } else if byte < 0xc0 {
      -1
    } else if byte < 0xe0 {
      1
    } else if byte < 0xf0 {
      2
    } else if byte < 0xf8 {
      3
    } else {
      -1
    }
    let mut code : Int? = if continuations < 0 {
      None
    } else if continuations == 0 {
      Some(byte)
    } else {
      Some(byte & (0x1f >> (continuations - 1)))
    }
    i += 1
    let mut k = 0
    while k < (if continuations > 0 { continuations } else { 0 }) &&
          code is Some(_) {
      let continuation = if i < length { octets[i] } else { 0 }
      if (continuation & 0xc0) == 0x80 {
        code = Some((code.unwrap() << 6) | (continuation & 0x3f))
        i += 1
      } else {
        code = None
      }
      k += 1
    }
    match
      wxmx_code_char(
        match code {
          Some(c) => int(c)
          None => Nil
        },
      ) {
      Char(c) => sb.write_char(c)
      _ => sb.write_char('?')
    }
  }
  Str(sb.to_string())
}

///|
/// The integer DIGITS spells in RADIX, or NIL if it spells none.
fn wxmx_parse_integer(digits : Value, radix : Value) -> Value raise {
  // (ignore-errors (parse-integer digits :radix radix)): surrounding
  // whitespace and a sign are allowed.
  let s = string_trim(" \t\n\r\u{0C}", lstring(digits))
  parse_integer(s, radix=to_int(radix)).unwrap_or(Nil)
}

///|
/// (vector-push-extend char string)
fn wxmx__push_char(string_ : Value, c : Char) -> Unit raise {
  vector_push_extend(Char(c), string_) |> ignore
}

///|
/// Push the character the XML reference &NAME; stands for onto STRING.  A
/// reference we do not know is copied through as it was written.
fn wxmx_push_reference(name : Value, string_ : Value) -> Value raise {
  let n = lstring(name)
  let chars = string_chars(n)
  let digits = chars.length() > 1 && chars[0] == '#'
  let hexadecimal = digits &&
    chars.length() > 2 &&
    (chars[1] == 'x' || chars[1] == 'X')
  let code : Value = if n == "lt" {
    Fix(60L)
  } else if n == "gt" {
    Fix(62L)
  } else if n == "amp" {
    Fix(38L)
  } else if n == "quot" {
    Fix(34L)
  } else if n == "apos" {
    Fix(39L)
  } else if hexadecimal {
    wxmx_parse_integer(Str(chars_to_string(chars[2:].to_array())), Fix(16L))
  } else if digits {
    wxmx_parse_integer(Str(chars_to_string(chars[1:].to_array())), Fix(10L))
  } else {
    Nil
  }
  match code {
    Fix(c) if c >= 0L && c < 0x110000L && wxmx__char_code_p(c.to_int()) =>
      wxmx__push_char(string_, Int::unsafe_to_char(c.to_int()))
    _ => {
      wxmx__push_char(string_, '&')
      for character in chars {
        wxmx__push_char(string_, character)
      }
      wxmx__push_char(string_, ';')
    }
  }
  Nil
}

///|
/// The characters of the XML text, converted once per string.
let wxmx__xml_cache : Ref[(String, Array[Char])?] = Ref(None)

///|
fn wxmx__xml_chars(xml : Value) -> Array[Char] raise {
  let s = lstring(xml)
  match wxmx__xml_cache.val {
    Some((k, cs)) if physical_equal(k, s) => cs
    _ => {
      let cs = string_chars(s)
      wxmx__xml_cache.val = Some((s, cs))
      cs
    }
  }
}

///|
/// Push the text XML holds between START and END onto STRING, resolving the
/// XML references in it.
fn wxmx_push_text(xml : Value, start : Value, end : Value, string_ : Value) -> Value raise {
  let cs = wxmx__xml_chars(xml)
  let end = to_int(end)
  let mut i = to_int(start)
  while i < end {
    let limit = if end < i + wxmx__reference_length {
      end
    } else {
      i + wxmx__reference_length
    }
    let mut semicolon = -1
    if cs[i] == '&' {
      for j in i..<limit {
        if cs[j] == ';' {
          semicolon = j
          break
        }
      }
    }
    if semicolon >= 0 {
      wxmx_push_reference(
        Str(chars_to_string(cs[i + 1:semicolon].to_array())),
        string_,
      )
      |> ignore
      i = semicolon + 1
    } else {
      wxmx__push_char(string_, cs[i])
      i += 1
    }
  }
  Nil
}

///|
/// `(search pattern xml :start2 start :end2 end)`, or -1.
fn wxmx__search(pattern : String, xml : Array[Char], start : Int, end : Int) -> Int {
  let p = string_chars(pattern)
  let mut i = start
  while i + p.length() <= end {
    let mut ok = true
    for j in 0..<p.length() {
      if xml[i + j] != p[j] {
        ok = false
        break
      }
    }
    if ok {
      return i
    }
    i += 1
  }
  -1
}

///|
/// Push the text of the <line> elements XML holds between START and END
/// onto STRING, one line each.
fn wxmx_push_lines(xml : Value, start : Value, end : Value, string_ : Value) -> Value raise {
  let cs = wxmx__xml_chars(xml)
  let end = to_int(end)
  let mut i = to_int(start)
  while true {
    let line = wxmx__search("<line>", cs, i, end)
    if line < 0 {
      return Nil
    }
    let close = {
      let c = wxmx__search("</line>", cs, line, end)
      if c < 0 {
        end
      } else {
        c
      }
    }
    wxmx_push_text(xml, int(line + 6), int(close), string_) |> ignore
    wxmx__push_char(string_, '\n')
    i = if end < close + 7 { end } else { close + 7 }
  }
  Nil
}

///|
/// (coerce string 'simple-string) of a character vector.
fn wxmx__simple_string(string_ : Value) -> Value raise {
  let sb = StringBuilder::new()
  let n = fill_pointer(string_)
  for i in 0..<n {
    match aref1(string_, i) {
      Char(c) => sb.write_char(c)
      _ => ()
    }
  }
  Str(sb.to_string())
}

///|
/// The Maxima input of the worksheet whose content.xml is XML: the text of
/// the <line> elements of every <input> element, in the order the worksheet
/// has them.  Everything else -- title, section and text cells, and the
/// stored output -- is not input and is left behind.
fn wxmx_content_input(xml : Value) -> Value raise {
  let cs = wxmx__xml_chars(xml)
  let string_ = make_array([0], elt="character", fill=0)
  let mut i = 0
  while true {
    let input = wxmx__search("<input>", cs, i, cs.length())
    if input < 0 {
      break
    }
    let close = {
      let c = wxmx__search("</input>", cs, input, cs.length())
      if c < 0 {
        cs.length()
      } else {
        c
      }
    }
    wxmx_push_lines(xml, int(input + 7), int(close), string_) |> ignore
    i = close
  }
  wxmx__simple_string(string_)
}

///|
/// The Maxima input stored in the .wxmx worksheet FILENAME.
fn wxmx_input_string(filename : Value) -> Value raise {
  let path = princ_to_string(filename)
  let stream = wxmx__open_octet_stream(path)
  let content = wxmx_stored_member(stream, Str("content.xml"), filename)
  if content is Nil {
    merr("~A holds no content.xml; it is not a .wxmx worksheet.", [Str(path)])
    |> ignore
  }
  wxmx_content_input(wxmx_utf_8_string(content))
}

///|
fn init_wxmx() -> Unit raise {
  ()
}
