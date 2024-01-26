permit(
  principal == a::"6\u{11}\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0",
  action in [Action::"action"],
  resource is a in a::"6\u{11}\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0"
) when {
  true
};
