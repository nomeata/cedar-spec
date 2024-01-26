permit(
  principal == a::"\u{10}\0\u{4}",
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && (((!false) == principal) == (true - Action::"action"))) && Action::"action") && Action::"action"
};
