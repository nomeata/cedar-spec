forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![Action::"action", context, false, context, Action::"action", principal]) in principal)) && principal
};
