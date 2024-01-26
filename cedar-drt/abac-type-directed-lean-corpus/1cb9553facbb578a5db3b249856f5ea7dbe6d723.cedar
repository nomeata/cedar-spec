forbid(
  principal is a in a::"666C",
  action in [Action::"action"],
  resource is a in a::"666C"
) when {
  (true && ((ip("6\0/\0\0\0\0\0+")).isIpv4())) && false
};
