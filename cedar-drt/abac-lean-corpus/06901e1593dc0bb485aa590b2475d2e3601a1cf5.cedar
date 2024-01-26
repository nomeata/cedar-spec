permit(
  principal,
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && ((false < Action::"action") || Action::"action")
};
