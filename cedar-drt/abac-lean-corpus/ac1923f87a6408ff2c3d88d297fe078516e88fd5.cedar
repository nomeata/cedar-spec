@L("")
@S("\u{12}\u{12}1\u{12}")
@SI("\u{12}\u{12}\u{12}\u{12}1\u{12}")
@r("")
@rII33("")
@s("\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}z\u{12}\u{14}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\0\0\0")
permit(
  principal is a,
  action in [Action::"action"],
  resource is a in a::",\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}?\u{12}z\u{12}\u{14}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\0\0\0\0\0"
) when {
  true && ((("" in false) in action) in ((true == false) == (false in principal)))
};
