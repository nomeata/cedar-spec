permit(
  principal == a::"\0",
  action in [Action::"action"],
  resource is a in a::"\0"
) when {
  true
};
