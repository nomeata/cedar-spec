forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && principal) && (false.containsAll(false.containsAll(action)))) && action
};
