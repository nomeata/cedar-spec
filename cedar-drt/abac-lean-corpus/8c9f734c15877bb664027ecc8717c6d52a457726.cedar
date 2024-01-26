forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a
) when {
  true && (!("\0\0\u{7}\0" is a))
};
