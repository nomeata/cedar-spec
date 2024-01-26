@p("\0\u{b}\0\0")
permit(
  principal == a::"\0L\0\0\0\0\u{b}\0",
  action in [Action::"action",Action::"action"],
  resource is a in a::"\0L\0\0\0\0\u{b}\0"
) when {
  true
};
