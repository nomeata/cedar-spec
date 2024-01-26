forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![false, "", a::"", principal, principal, principal]) is a)) && principal
};
