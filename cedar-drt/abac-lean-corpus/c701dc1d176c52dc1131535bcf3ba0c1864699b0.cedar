forbid(
  principal is a in a::"\0\0\0\0\0\0\0\0z\0\u{7}\0\0",
  action in [Action::"action"],
  resource == a::"\0\0\0\0\0\0\0\0z\0\u{7}\0\0"
) when {
  true
};
