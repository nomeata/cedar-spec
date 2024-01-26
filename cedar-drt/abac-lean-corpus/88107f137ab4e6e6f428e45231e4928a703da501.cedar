permit(
  principal is a,
  action in [Action::"action"],
  resource == a::""
) when {
  (true && Action::"action") && principal
};
