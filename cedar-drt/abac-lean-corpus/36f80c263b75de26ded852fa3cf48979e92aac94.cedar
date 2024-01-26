permit(
  principal == a::"jij",
  action in [Action::"action"],
  resource == a::"jij"
) when {
  true && principal
};
