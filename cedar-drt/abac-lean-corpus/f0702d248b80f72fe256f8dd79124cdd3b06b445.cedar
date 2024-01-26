forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![true, false, resource, A::""]) is a)) && principal
};
