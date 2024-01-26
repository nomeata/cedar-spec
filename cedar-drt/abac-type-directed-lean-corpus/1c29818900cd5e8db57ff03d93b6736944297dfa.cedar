permit(
  principal == a::"6\0\u{11}\0\0\0\0\0\0\0\0\0\0\0/\t\t\0\0\u{1}\u{b}\0",
  action in [Action::"action"],
  resource is a in a::"6\0\u{11}\0\0\0\0\0\0\0\0\0\0\0/\t\t\0\0\u{1}\u{b}\0"
) when {
  true
};
