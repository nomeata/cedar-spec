forbid(
  principal == a::"66\u{1}\0\0\u{1}\0\0@\0e6\0\u{1}",
  action in [Action::"action"],
  resource == a::""
) when {
  true
};
