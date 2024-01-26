forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((resource in a::"6") || false)) && false) && false
};
