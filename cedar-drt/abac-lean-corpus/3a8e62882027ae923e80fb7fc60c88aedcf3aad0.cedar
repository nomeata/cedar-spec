forbid(
  principal == a::"\0\0\0\0\0\0\0\u{1}\0\0\0\0",
  action in [Action::"action",Action::"action"],
  resource
) when {
  true
};
