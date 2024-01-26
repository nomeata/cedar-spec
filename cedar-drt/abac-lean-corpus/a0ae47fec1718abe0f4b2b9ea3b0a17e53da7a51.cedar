permit(
  principal == a::"]",
  action in [Action::"action"],
  resource is a
) when {
  true && [principal, false, principal, action, Action::"action"]
};
