forbid(
  principal is a in a::"\0\0\0\0\0\0\0\0\0\0\0\u{f}",
  action,
  resource == a::"\0\0\0\0\0\0\0\0\0\0\0\u{f}"
) when {
  (true && principal) && principal
};
