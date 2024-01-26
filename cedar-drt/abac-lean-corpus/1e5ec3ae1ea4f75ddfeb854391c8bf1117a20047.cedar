permit(
  principal == a::"s",
  action in [Action::"action"],
  resource == a::"s"
) when {
  true && principal
};
