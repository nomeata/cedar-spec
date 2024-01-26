permit(
  principal is a in a::"/6",
  action == Action::"action",
  resource
) when {
  (true && ((if ((ip("::28:900:41b5:b5b5:b5b5")).isIpv6()) then (ip("0.0.0.0")) else (ip("0.0.0.0"))).isIpv6())) && false
};
