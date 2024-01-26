forbid(
  principal is a,
  action in [Action::"action"],
  resource == a::""
) when {
  true && (!(a::"\0\u{10}\0\0\0\0" < a::""))
};
