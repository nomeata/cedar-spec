forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![false, action, principal, principal, principal, principal]) is a)) && principal
};
