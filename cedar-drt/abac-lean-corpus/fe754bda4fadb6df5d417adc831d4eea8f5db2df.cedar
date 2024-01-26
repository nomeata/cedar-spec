permit(
  principal == a::"j\0\0\0\0",
  action in [Action::"action",Action::"action"],
  resource is a in a::"j\0\0\0\0"
) when {
  true
};
