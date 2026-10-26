///|
fn main {
  let code = @core.cli_main(@env.args())
  @core.exit(code)
}
