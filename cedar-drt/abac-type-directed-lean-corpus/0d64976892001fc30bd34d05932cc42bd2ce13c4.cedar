permit(
  principal,
  action in [Action::"action",Action::"action"],
  resource is a
) when {
  false && ((if (principal in principal) then (ip("9.9.217.9")) else (ip("0.0.0.0"))).isLoopback())
};
