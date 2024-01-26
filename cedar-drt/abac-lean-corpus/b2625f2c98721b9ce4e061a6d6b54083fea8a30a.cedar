forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![Action::"action", resource, false, resource, resource, resource]) is a)) && ""
};
