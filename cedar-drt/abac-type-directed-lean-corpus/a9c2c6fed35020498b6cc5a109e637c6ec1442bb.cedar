permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && ((if ((ip("54e54.54.54")).isIpv4()) then (ip("0.0.0.0")) else (ip("0.0.0.0"))).isIpv6())) && false
};
