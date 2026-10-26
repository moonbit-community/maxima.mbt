///|
fn main {
  // Maxima recurses deeply (the simplifier, the reader, the f2cl
  // libraries): run it on a thread with a 512 MB stack.
  let code = Ref(0)
  @lisp.run_with_stack(0x20000000L, () => code.val = @core.cli_main(@env.args()))
  @core.exit(code.val)
}
