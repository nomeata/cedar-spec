forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && [principal, principal, action, [[false, principal, principal, principal], principal, principal, principal, principal, principal]]) && principal
};
