forbid(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  (true && ((ip("87.255.255.209/4")).isIpv6())) && false
};
