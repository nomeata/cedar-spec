forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource is a
) when {
  (true && ((ip("6")).isIpv4())) && (a::"" in principal)
};
