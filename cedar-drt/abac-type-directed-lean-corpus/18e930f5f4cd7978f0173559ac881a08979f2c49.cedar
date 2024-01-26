forbid(
  principal == a::"",
  action in [Action::"action"],
  resource == a::"66\u{1}\0\0\u{1}\0\0\t\0e6\0\u{1}"
) when {
  true
};
