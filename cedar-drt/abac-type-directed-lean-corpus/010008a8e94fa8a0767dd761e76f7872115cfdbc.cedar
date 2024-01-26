permit(
  principal == a::"666\t6\u{1}\0\u{1}6\0",
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  true
};
