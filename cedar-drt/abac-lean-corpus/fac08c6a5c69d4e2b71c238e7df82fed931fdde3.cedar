permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((Action::"action" == (true.greaterThanOrEqual(context))).containsAny(principal))) && context
};
