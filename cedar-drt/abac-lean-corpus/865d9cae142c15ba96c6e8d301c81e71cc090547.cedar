permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::"\u{10}\0\u{4}"
) when {
  ((true && (((!false) == principal) == (Action::"action" - Action::"action"))) && Action::"action") && Action::"action"
};
