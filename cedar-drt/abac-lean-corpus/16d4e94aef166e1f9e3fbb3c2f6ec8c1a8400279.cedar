@Afe01("")
permit(
  principal is a in a::"j\0\u{10}",
  action in [Action::"action",Action::"action",Action::"action"],
  resource == a::""
) when {
  true
};
