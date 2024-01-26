forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![true, false, resource, false]) is a)) && principal
};
