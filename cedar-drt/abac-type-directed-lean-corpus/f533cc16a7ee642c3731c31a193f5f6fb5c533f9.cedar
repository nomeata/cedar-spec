permit(
  principal,
  action in [Action::""],
  resource
) when {
  ((true && ((ip(principal["r"])).isIpv6())) && false) && false
};
