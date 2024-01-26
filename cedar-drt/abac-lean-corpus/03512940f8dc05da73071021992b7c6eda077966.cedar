forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && [a::"", action, !(!action), !(!action), !(!action), [principal, principal, principal, principal, a::"", principal]]) && principal
};
