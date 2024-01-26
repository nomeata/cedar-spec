forbid(
  principal is a in a::"J",
  action in [Action::"action"],
  resource is a in a::"J"
) when {
  true && (!("\0\0\u{7}\0" is a))
};
