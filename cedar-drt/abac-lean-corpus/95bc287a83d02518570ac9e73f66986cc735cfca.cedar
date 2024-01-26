forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![Action::"action", true, true, "", false, principal]) in principal)) && principal
};
