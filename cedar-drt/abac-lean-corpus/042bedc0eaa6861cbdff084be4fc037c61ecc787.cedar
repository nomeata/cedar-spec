forbid(
  principal is a in a::"j\0\0\0",
  action in [Action::"action"],
  resource == a::"j\0\0\0"
) when {
  false && principal
};
