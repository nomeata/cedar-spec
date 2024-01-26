permit(
  principal == a::"\0\0\0",
  action in [Action::"action"],
  resource is a
) when {
  true
};
