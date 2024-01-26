permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && (a::"\u{10}\0\u{4}" && action)) && Action::"action") && action
};
