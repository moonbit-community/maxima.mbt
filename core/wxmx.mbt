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
// The generated contract has no declarations for this file; its functions
// are file-private (`wxmx__*`).  The binary input stream is the file's
// octets with a read position.

///|
/// The signature of a .zip local file header, "PK\3\4" read as a
/// little-endian 32 bit integer.
let wxmx__local_file_header : Int64 = 0x04034b50L

///|
/// An octet input stream over a whole file.
priv struct WxmxStream {
  data : Bytes
  mut pos : Int
}

///|
fn wxmx__read_byte(stream : WxmxStream) -> Int? {
  if stream.pos < stream.data.length() {
    let b = stream.data[stream.pos].to_int()
    stream.pos += 1
    Some(b)
  } else {
    None
  }
}

///|
/// Read a little-endian 16 bit unsigned integer.  None at end of file.
fn wxmx__read_u16(stream : WxmxStream) -> Int64? {
  let low = wxmx__read_byte(stream)
  let high = match low {
    Some(_) => wxmx__read_byte(stream)
    None => None
  }
  match (low, high) {
    (Some(l), Some(h)) => Some((l | (h << 8)).to_int64())
    _ => None
  }
}

///|
/// Read a little-endian 32 bit unsigned integer.  None at end of file.
fn wxmx__read_u32(stream : WxmxStream) -> Int64? {
  let low = wxmx__read_u16(stream)
  let high = match low {
    Some(_) => wxmx__read_u16(stream)
    None => None
  }
  match (low, high) {
    (Some(l), Some(h)) => Some(l | (h << 16))
    _ => None
  }
}

///|
/// Read COUNT octets.  None if the stream does not hold that many -- a
/// size a damaged header overstates is not to be allocated first and found
/// out about afterwards.
fn wxmx__read_octets(stream : WxmxStream, count : Int64) -> Bytes? {
  let length = stream.data.length().to_int64()
  if !(count <= length - stream.pos.to_int64()) {
    return None
  }
  let n = count.to_int()
  let octets = stream.data[stream.pos:stream.pos + n].to_bytes()
  stream.pos += n
  Some(octets)
}

///|
/// Move COUNT octets forward in STREAM.
fn wxmx__skip(stream : WxmxStream, count : Int64) -> Unit {
  // (file-position stream (+ (file-position stream) count)); a position
  // past the end leaves the stream at end of file.
  let p = stream.pos.to_int64() + count
  stream.pos = if p > stream.data.length().to_int64() {
    stream.data.length()
  } else {
    p.to_int()
  }
}

///|
/// The name a .zip local file header stores, as a string.  Member names
/// are UTF-8 or CP437; the ones we look for are plain ASCII, where the two
/// agree.
fn wxmx__member_name(octets : Bytes) -> String {
  let sb = StringBuilder::new()
  for b in octets {
    sb.write_char(Int::unsafe_to_char(b.to_int()))
  }
  sb.to_string()
}

///|
/// Return the contents of the archive member NAME of the .zip file open
/// on STREAM as octets, or None if there is no such member.  FILENAME names
/// the archive in error messages.
fn wxmx__stored_member(
  stream : WxmxStream,
  name : String,
  filename : Value,
) -> Bytes? raise {
  while true {
    match wxmx__read_u32(stream) {
      Some(sig) if sig == wxmx__local_file_header => ()
      // Either the end of the last member's data, where the central
      // directory begins, or a truncated file.  Either way there is no
      // further local file header to read.
      _ => return None
    }
    wxmx__read_u16(stream) |> ignore // version needed to extract
    let flags = wxmx__read_u16(stream)
    let method_ = wxmx__read_u16(stream)
    wxmx__read_u32(stream) |> ignore // modification time and date
    wxmx__read_u32(stream) |> ignore // CRC-32
    let compressed_size = wxmx__read_u32(stream)
    wxmx__read_u32(stream) |> ignore // uncompressed size
    let name_length = wxmx__read_u16(stream)
    let extra_length = wxmx__read_u16(stream)
    let member = match (extra_length, name_length) {
      (Some(_), Some(nl)) => wxmx__read_octets(stream, nl)
      _ => None
    }
    let member = match member {
      Some(m) => m
      None => return None
    }
    wxmx__skip(stream, extra_length.unwrap_or(0L))
    // Bit 3 of the flags moves the sizes behind the member's data, into a
    // data descriptor, and leaves zeroes here.  Then there is nothing to
    // skip the member by.
    let flag3 = (flags.unwrap_or(0L) & 8L) != 0L
    if name == wxmx__member_name(member) {
      if method_ != Some(0L) {
        merr(
          "Cannot read the .wxmx worksheet ~A: its ~A is stored compressed, which needs a .zip decompressor.",
          [filename, Str(name)],
        )
        |> ignore
      } else if flag3 {
        merr(
          "Cannot read the .wxmx worksheet ~A: its ~A does not record its size, which needs a full .zip reader.",
          [filename, Str(name)],
        )
        |> ignore
      } else {
        return wxmx__read_octets(stream, compressed_size.unwrap_or(0L))
      }
    } else if flag3 {
      merr(
        "Cannot read the .wxmx worksheet ~A: the member ~A ahead of ~A does not record its size, which needs a full .zip reader.",
        [filename, Str(wxmx__member_name(member)), Str(name)],
      )
      |> ignore
    } else {
      wxmx__skip(stream, compressed_size.unwrap_or(0L))
    }
  }
  None
}

///|
/// The character of code point CODE, or a question mark where there is
/// none.
fn wxmx__code_char(code : Int?) -> Char {
  match code {
    Some(c) if c >= 0 && c < 0x110000 && !(c >= 0xd800 && c < 0xe000) =>
      Int::unsafe_to_char(c)
    _ => '?'
  }
}

///|
/// Decode OCTETS, a UTF-8 encoded archive member, into a string.  A
/// malformed sequence, and a character with no code point, become a
/// question mark.
fn wxmx__utf_8_string(octets : Bytes) -> String {
  let length = octets.length()
  let sb = StringBuilder::new()
  let mut i = 0
  while i < length {
    let byte = octets[i].to_int()
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
      let continuation = if i < length { octets[i].to_int() } else { 0 }
      if (continuation & 0xc0) == 0x80 {
        code = Some((code.unwrap() << 6) | (continuation & 0x3f))
        i += 1
      } else {
        code = None
      }
      k += 1
    }
    sb.write_char(wxmx__code_char(code))
  }
  sb.to_string()
}

///|
/// The integer DIGITS spells in RADIX, or None if it spells none.
fn wxmx__parse_integer(digits : String, radix : Int) -> Int? {
  if digits.length() == 0 {
    return None
  }
  let mut n = 0L
  let mut neg = false
  let mut start = 0
  let first = digits.get_char(0).unwrap()
  if first == '+' || first == '-' {
    neg = first == '-'
    start = 1
    if digits.length() == 1 {
      return None
    }
  }
  for c in digits.view(start_offset=start) {
    let d = if c >= '0' && c <= '9' {
      c.to_int() - '0'.to_int()
    } else if c >= 'a' && c <= 'z' {
      c.to_int() - 'a'.to_int() + 10
    } else if c >= 'A' && c <= 'Z' {
      c.to_int() - 'A'.to_int() + 10
    } else {
      return None
    }
    if d >= radix {
      return None
    }
    n = n * radix.to_int64() + d.to_int64()
    if n > 0x7fffffffL {
      // Far beyond any character code: no character.
      return Some(0x7fffffff)
    }
  }
  Some(if neg { -n.to_int() } else { n.to_int() })
}

///|
/// Push the character the XML reference &NAME; stands for onto STRING.  A
/// reference we do not know is copied through as it was written.
fn wxmx__push_reference(name : String, string : StringBuilder) -> Unit {
  let chars = name.to_array()
  let digits = chars.length() > 1 && chars[0] == '#'
  let hexadecimal = digits &&
    chars.length() > 2 &&
    (chars[1] == 'x' || chars[1] == 'X')
  let code = if name == "lt" {
    Some(60)
  } else if name == "gt" {
    Some(62)
  } else if name == "amp" {
    Some(38)
  } else if name == "quot" {
    Some(34)
  } else if name == "apos" {
    Some(39)
  } else if hexadecimal {
    wxmx__parse_integer(String::from_array(chars[2:]), 16)
  } else if digits {
    wxmx__parse_integer(String::from_array(chars[1:]), 10)
  } else {
    None
  }
  match code {
    Some(c) if c >= 0 && c < 0x110000 && !(c >= 0xd800 && c < 0xe000) =>
      string.write_char(Int::unsafe_to_char(c))
    _ => {
      string.write_char('&')
      string.write_string(name)
      string.write_char(';')
    }
  }
}

///|
/// An XML reference is short: &thisisnotareference; in a text cell must
/// not swallow the text that follows it looking for a semicolon.
let wxmx__reference_length : Int = 12

///|
/// Push the text XML holds between START and END onto STRING, resolving
/// the XML references in it.
fn wxmx__push_text(
  xml : Array[Char],
  start : Int,
  end : Int,
  string : StringBuilder,
) -> Unit {
  let mut i = start
  while i < end {
    let limit = if end < i + wxmx__reference_length {
      end
    } else {
      i + wxmx__reference_length
    }
    let mut semicolon = -1
    if xml[i] == '&' {
      for j in i..<limit {
        if xml[j] == ';' {
          semicolon = j
          break
        }
      }
    }
    if semicolon >= 0 {
      wxmx__push_reference(String::from_array(xml[i + 1:semicolon]), string)
      i = semicolon + 1
    } else {
      string.write_char(xml[i])
      i += 1
    }
  }
}

///|
/// `(search pattern xml :start2 start :end2 end)`, or -1.
fn wxmx__search(
  pattern : String,
  xml : Array[Char],
  start : Int,
  end : Int,
) -> Int {
  let p = pattern.to_array()
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
fn wxmx__push_lines(
  xml : Array[Char],
  start : Int,
  end : Int,
  string : StringBuilder,
) -> Unit {
  let mut i = start
  while true {
    let line = wxmx__search("<line>", xml, i, end)
    if line < 0 {
      return
    }
    let close = {
      let c = wxmx__search("</line>", xml, line, end)
      if c < 0 {
        end
      } else {
        c
      }
    }
    wxmx__push_text(xml, line + 6, close, string)
    string.write_char('\n')
    i = if end < close + 7 { end } else { close + 7 }
  }
}

///|
/// The Maxima input of the worksheet whose content.xml is XML: the text of
/// the <line> elements of every <input> element, in the order the worksheet
/// has them.  Everything else -- title, section and text cells, and the
/// stored output -- is not input and is left behind.
fn wxmx__content_input(xml_string : String) -> String {
  let xml = xml_string.to_array()
  let string = StringBuilder::new()
  let mut i = 0
  while true {
    let input = wxmx__search("<input>", xml, i, xml.length())
    if input < 0 {
      break
    }
    let close = {
      let c = wxmx__search("</input>", xml, input, xml.length())
      if c < 0 {
        xml.length()
      } else {
        c
      }
    }
    wxmx__push_lines(xml, input + 7, close, string)
    i = close
  }
  string.to_string()
}

///|
/// The Maxima input stored in the .wxmx worksheet FILENAME.
fn wxmx__input_string(filename : Value) -> Value raise {
  let path = princ_to_string(filename)
  let stream : WxmxStream = { data: @lisp.read_file_bytes(path), pos: 0 }
  let content = wxmx__stored_member(stream, "content.xml", Str(path))
  match content {
    Some(c) => Str(wxmx__content_input(wxmx__utf_8_string(c)))
    None =>
      merr("~A holds no content.xml; it is not a .wxmx worksheet.", [
        Str(path),
      ])
  }
}
