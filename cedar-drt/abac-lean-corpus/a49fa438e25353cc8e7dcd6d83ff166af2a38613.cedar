forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![principal, principal, "j", false]) is a)) && principal
};
