forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![Action::"action", context, false, context, "", false]) in principal)) && principal
};
