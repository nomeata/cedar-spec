forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((action in action) || true)) && false) && false
};
