forbid(
  principal == a::"",
  action == Action::"action",
  resource is a in a::""
) when {
  (true && ((ip("7$")).isIpv4())) && ((if ((decimal("-04572769783788.327")).lessThanOrEqual(decimal("0.0"))) then (ip("0.0.0.0")) else (ip("0.0.0.0"))).isIpv4())
};
