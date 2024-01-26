forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((![Action::"action", principal, principal, "\u{16}\u{16}\u{16}\u{16}\u{16}d", true, action]) in [!principal, action, [Action::"action", principal, principal, principal, principal, principal], principal, principal, principal])) && principal
};
