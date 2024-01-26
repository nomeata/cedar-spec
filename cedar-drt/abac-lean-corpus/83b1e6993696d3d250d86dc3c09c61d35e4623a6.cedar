forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (false && principal) && true
};
