permit(
  principal,
  action in [B::Action::"action"],
  resource is B::a in B::a::""
) when {
  (true && ((if ((ip("255.110.54.108")).isIpv4()) then (ip("0.0.0.0")) else (ip("0.0.0.0"))).isIpv4())) && false
};
