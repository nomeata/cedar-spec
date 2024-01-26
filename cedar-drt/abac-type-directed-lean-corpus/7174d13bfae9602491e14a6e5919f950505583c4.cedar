forbid(
  principal is a in a::"66",
  action in [Action::"action"],
  resource is a in a::"66"
) when {
  (true && ((ip("")).isIpv4())) && false
};
