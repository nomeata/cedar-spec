permit(
  principal == a::"kj\0",
  action in [Action::"action"],
  resource is a
) when {
  true
};
