forbid(
  principal,
  action in [Action::"action"],
  resource is a in a::"i\0\0\u{16}"
) when {
  false && principal
};
