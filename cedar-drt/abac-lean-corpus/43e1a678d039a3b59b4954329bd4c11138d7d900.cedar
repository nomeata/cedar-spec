permit(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  true && [false, context, [a::"", {"Khhh": a::""}, a::"", context, false, principal], principal, principal, principal]
};
