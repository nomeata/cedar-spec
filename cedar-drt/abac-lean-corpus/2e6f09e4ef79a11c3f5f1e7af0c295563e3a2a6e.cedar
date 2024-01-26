forbid(
  principal is a,
  action in [Action::"action"],
  resource == a::"jj"
) when {
  (true && (([a::"", true, a::"", Action::"action", context, resource].containsAll([a::"", Action::"action", a::"jj", context, a::"jj", principal, principal])) == principal)) && principal
};
