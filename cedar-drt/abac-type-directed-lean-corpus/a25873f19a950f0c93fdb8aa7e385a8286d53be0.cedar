permit(
  principal,
  action in [Action::"action",Action::"action"],
  resource is a in a::""
) when {
  (true && (Action::"action" in [Action::"action", principal, principal])) && true
};
