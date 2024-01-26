forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (a::"" in [[false, principal], principal])) && principal) && principal
};
