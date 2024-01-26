forbid(
  principal is a in a::"\0\0\0\u{8}j&j\0\0",
  action in [Action::"action"],
  resource == a::"\0\0\0\u{8}j&j\0\0"
) when {
  (true && a::"\0\0\0\u{8}j&j\0\0") && false
};
