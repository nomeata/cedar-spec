permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((Action::"action" == (true.greaterThanOrEqual(principal))).containsAny(principal))) && principal
};
