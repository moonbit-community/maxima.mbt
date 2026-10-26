// Port of src/verify-html-index.lisp: verification of the HTML index
// entries against the text (info) entries.  Use command-line option
// --verify-html-index to perform this verification.

///|
/// spec-chars-string are the special characters that texinfo converted to
/// lower-case hex digits representing the char-code of the character.
let verify_html_index__spec_chars_string : String = "_.%$?,<>#=:;*-^+/'()[]!@|`~\\"

///|
/// The (code . replacement) regex pairs of HANDLE-SPECIAL-CHARS, computed
/// once.
let verify_html_index__pairs : Ref[Array[(Value, Value)]?] = Ref(None)

///|
fn verify_html_index__code_pairs() -> Array[(Value, Value)] raise {
  match verify_html_index__pairs.val {
    Some(p) => p
    None => {
      let pairs : Array[(Value, Value)] = []
      for c in verify_html_index__spec_chars_string {
        // Bug in pregexp?  If we pregexp-quote "$" (to "\\$"), when we try
        // to replace the match with "\\$", we end up with an empty string.
        // So don't quote this character.
        let regexp_quoted : Value = if c == '$' {
          Str(c.to_string())
        } else {
          rx_pregexp_quote(Str(c.to_string()))
        }
        let code = rx_pregexp_quote(
          Str(
            string_downcase(
              format_to_string("_~4,'0x", [int(c.to_int())]),
            ),
          ),
        )
        pairs.push((code, regexp_quoted))
      }
      verify_html_index__pairs.val = Some(pairs)
      pairs
    }
  }
}

///|
/// Handle special encoded characters in HTML file.  Texinfo encodes special
/// characters to hexadecimal form and this needs to be undone so we know
/// what the actual character is when looking up the documentation.
fn handle_special_chars(item : Value) -> Value raise {
  let mut item = item
  for p in verify_html_index__code_pairs() {
    // Exit early if there are not "_" characters left in the topic
    if !lstring(item).contains("_") {
      break
    }
    item = rx_pregexp_replace_star(p.0, item, p.1)
  }
  item
}

///|
fn get_html_topics() -> Value raise {
  // Find all the HTML entries and place in a list.
  let topics = Collector::new()
  maphash((topic, _v) => topics.add(topic), symval(q_ear_html_index))
  set(q_ear_html_topics, topics.result())
}

///|
fn get_text_topics() -> Value raise {
  // Find all the text entries and place in a list.
  let text_topics = symval(q_ear_text_topics)
  clrhash(text_topics) |> ignore
  maphash(
    (_k, v) => for table in v.iter() {
      // We don't care what the value is.
      maphash((topic, _v) => sethash(topic, text_topics, t) |> ignore, table)
    },
    symval(q_ear_info_tables),
  )
  Nil
}

///|
fn verify_html_index() -> Value raise {
  let html_index = symval(q_ear_html_index)
  let text_topics = symval(q_ear_text_topics)
  // Make sure the hash table has the correct test!  This is important.
  match html_index {
    Hash(h) if h.kind != HashTest::Equal =>
      mwarning(
        list1(
          format(Nil, "HTML index hash table test must be `equal not ~S~%", [
            Str(
              match h.kind {
                HashTest::Eq => "EQ"
                HashTest::Eql => "EQL"
                HashTest::Equal => "EQUAL"
                HashTest::Equalp => "EQUALP"
              },
            ),
          ]),
        ),
      )
      |> ignore
    _ => ()
  }
  get_html_topics() |> ignore
  get_text_topics() |> ignore
  // The text entries are the source of truth about documentation.  Print
  // out differences between the html entries and the text entries.
  if hash_table_count(html_index) != hash_table_count(text_topics) {
    mwarning(
      list1(
        format(
          Nil,
          "Number of HTML entries (~A) does not match text entries (~A)~%",
          [int(hash_table_count(html_index)), int(hash_table_count(text_topics))],
        ),
      ),
    )
    |> ignore
  }
  // If the set of topics differs between HTML and text, print out the
  // differences.
  let extra = Collector::new()
  maphash(
    (key, _v) => if gethash(key, text_topics) is Nil { extra.add(key) },
    html_index,
  )
  set(q_ear_extra_html_entries, extra.result()) |> ignore
  let missing = Collector::new()
  maphash(
    (key, _v) => if !gethash2(key, html_index).1 { missing.add(key) },
    text_topics,
  )
  set(q_ear_missing_html_entries, missing.result()) |> ignore
  let maybe_print_warning = (prefix_msg : String, diffs : Value) => {
    let max_display_length = 20
    if diffs.truthy() {
      let diff_length = length(diffs)
      let displayed_length = if diff_length < max_display_length {
        diff_length
      } else {
        max_display_length
      }
      let s = make_string_output_stream()
      format(s, "~D ~A:~% ~{~S~^ ~}", [
        int(length(diffs)),
        Str(prefix_msg),
        list(list_to_array(diffs)[0:displayed_length].to_array()),
      ])
      |> ignore
      if diff_length > max_display_length {
        format(s, "... plus ~D more", [int(diff_length - max_display_length)])
        |> ignore
      }
      format(s, "~%", []) |> ignore
      mwarning(list1(Str(get_output_stream_string(s)))) |> ignore
    }
  }
  maybe_print_warning(
    "HTML entries not in text entries",
    symval(q_ear_extra_html_entries),
  )
  maybe_print_warning(
    "Text entries not in HTML entries",
    symval(q_ear_missing_html_entries),
  )
  // Return true if there a no extra or missing entries.
  lbool(
    !(
      symval(q_ear_extra_html_entries).truthy() ||
      symval(q_ear_missing_html_entries).truthy()
    ),
  )
}

///|
/// Undocumented Maxima function to verify the HTML index so it can be
/// easily run from the REPL.  Mostly for debugging.  The optional arg TIMEP
/// will call TIME to show how long it took to run the verification.
fn d_verify_html_index(timep? : Value = Nil) -> Value raise {
  if timep.truthy() {
    // (time (verify-html-index))
    let t0 = cpu_time()
    let w0 = wall_time_ms()
    let r = verify_html_index()
    let run = cpu_time() - t0
    let real = (wall_time_ms() - w0).to_double() / 1000.0
    format(
      symval(sym("*trace-output*")),
      "~&Evaluation took:~%  ~,3F seconds of real time~%  ~,6F seconds of total run time~%",
      [Flo(real), Flo(run)],
    )
    |> ignore
    r
  } else {
    verify_html_index()
  }
}

///|
fn init_verify_html_index() -> Unit raise {
  defvar_init(q_ear_text_topics, make_hash_table(kind=HashTest::Equal))
}
