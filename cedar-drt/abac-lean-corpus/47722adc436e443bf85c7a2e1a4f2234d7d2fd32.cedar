forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![Action::"action", context, a::"", Action::"action", A00::"", principal]) in principal)) && principal
};
