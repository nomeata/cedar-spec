permit(
  principal == a::"\0\0",
  action == Action::"action",
  resource is a in a::"\0\0"
) when {
  (true && ((ip("Â.0.0.0")).isIpv6())) && false
};
