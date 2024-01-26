forbid(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::"\0\0\0\0\0\0\0\0\0\0\0*\u{16}"
) when {
  true
};
