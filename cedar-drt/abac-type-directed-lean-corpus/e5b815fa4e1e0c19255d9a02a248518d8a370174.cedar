forbid(
  principal == a::"66",
  action == Action::"action",
  resource
) when {
  (true && ((ip("202.54.54.54/4")).isIpv4())) && false
};
