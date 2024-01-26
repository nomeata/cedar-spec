forbid(
  principal == a::"\0\0\0\0\0\0\0\0\u{12}ei",
  action in [Action::"action"],
  resource is a in a::"\0\0\0\0\0\0\0\0\u{12}ei"
) when {
  false
};
