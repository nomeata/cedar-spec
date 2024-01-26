permit(
  principal == a::"jij",
  action in [Action::"action"],
  resource in a::""
) when {
  true && principal
};
