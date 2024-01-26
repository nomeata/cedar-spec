forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ([action].contains(Action::"action"))) && true) && false
};
