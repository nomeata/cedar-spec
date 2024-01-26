permit(
  principal == a::"6666\u{1}\0\0\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource is a in a::"6666\u{1}\0\0\0"
) when {
  false
};
