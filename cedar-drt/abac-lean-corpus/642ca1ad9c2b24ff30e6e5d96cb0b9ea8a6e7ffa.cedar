permit(
  principal == a::"j\0\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"j\0\0\0\0"
) when {
  true && a::"j\0\0\0\0"
};
