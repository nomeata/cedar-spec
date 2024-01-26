permit(
  principal == a::"\0",
  action in [Action::"action"],
  resource in a::""
) when {
  true
};
