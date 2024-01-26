permit(
  principal == a::"&\u{11}\0\0",
  action in [Action::"action"],
  resource is a in a::"&\u{11}\0\0"
) when {
  true
};
