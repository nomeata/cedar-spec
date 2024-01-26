forbid(
  principal == a::"6\0\'\0\0&\u{1}\0\0",
  action == Action::"action",
  resource is a in a::"6\0\'\0\0&\u{1}\0\0"
) when {
  false
};
