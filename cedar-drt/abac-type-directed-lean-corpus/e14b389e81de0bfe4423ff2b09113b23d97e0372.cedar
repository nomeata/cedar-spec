permit(
  principal == a::"\u{8}\0ef\u{1}\0\0",
  action == Action::"action",
  resource is a in a::"\u{8}\0ef\u{1}\0\0"
) when {
  true
};
