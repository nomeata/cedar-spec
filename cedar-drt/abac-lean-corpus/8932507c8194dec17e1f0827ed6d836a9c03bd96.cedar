forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![Action::"action", resource, A::"", principal, principal, principal]) is a)) && principal
};
