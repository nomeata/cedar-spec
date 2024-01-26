permit(
  principal == a::"G",
  action in [Action::"action"],
  resource is a
) when {
  true && action
};
