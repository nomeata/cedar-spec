forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![principal, a::"", Action::"action", A::""]) is a)) && principal
};
