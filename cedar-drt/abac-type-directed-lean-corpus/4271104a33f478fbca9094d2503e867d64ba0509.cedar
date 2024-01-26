permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((if ((ip("599..5544.201.202/18")).isIpv4()) then (ip("0.0.0.0")) else (ip("0.0.0.0"))).isIpv4())) && false) && false
};
