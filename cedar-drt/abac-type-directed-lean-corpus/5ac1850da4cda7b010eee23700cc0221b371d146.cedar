permit(
  principal == a::"66",
  action in [Action::"action"],
  resource is a in a::"66"
) when {
  true
};
