forbid(
  principal is a in a::"\u{15}",
  action == Action::"action",
  resource == a::""
) when {
  ((true && a::"") && Action::"action") && a::""
};
