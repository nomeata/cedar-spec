permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && [false, principal, false, true, a::""]) && a::""
};
