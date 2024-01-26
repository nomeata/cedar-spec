forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![Action::"action", context, A::"", principal, principal, principal]) in principal)) && principal
};
