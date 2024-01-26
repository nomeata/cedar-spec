forbid(
  principal,
  action == Action::"action",
  resource == a::"j\0\0\0\0\0"
) when {
  (true && action) && false
};
