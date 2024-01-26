forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![true, a::"", true, Action::"action", true, false]) is a)) && principal
};
