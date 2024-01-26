permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && Action::"action") && Action::"action"
};
