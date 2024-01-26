permit(
  principal in a::"r",
  action in [Action::"action"],
  resource == a::"r"
) when {
  (true && (context.containsAny(a::""))) && principal
};
