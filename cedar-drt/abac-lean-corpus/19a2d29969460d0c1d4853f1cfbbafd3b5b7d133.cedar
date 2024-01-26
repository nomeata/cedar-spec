permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((Action::"action" == (decimal(""))).containsAny(principal))) && principal
};
