permit(
  principal == a::"j\0\0\0",
  action in [Action::"action"],
  resource
) when {
  true && context
};
