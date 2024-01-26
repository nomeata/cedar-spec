permit(
  principal in a::"r",
  action in [Action::"action"],
  resource == a::"r"
) when {
  (true && [[a::"", a::""][""], a::""]) && a::""
};
