forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![a::"", context, Action::"action", principal, context, Action::"action"]) in principal)) && principal
};
