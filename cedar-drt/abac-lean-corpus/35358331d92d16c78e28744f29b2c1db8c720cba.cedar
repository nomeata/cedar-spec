forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && [Action::"action", [a::"", true, false, principal, principal, principal], principal, principal, principal, principal]) && principal
};
