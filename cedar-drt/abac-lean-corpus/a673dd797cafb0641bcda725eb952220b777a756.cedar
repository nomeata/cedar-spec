permit(
  principal is a,
  action in [Action::"action"],
  resource == a::""
) when {
  true && [false, context, [a::"", [Action::"action", a::"", a::""], context, a::"", principal, principal], principal, principal, principal]
};
