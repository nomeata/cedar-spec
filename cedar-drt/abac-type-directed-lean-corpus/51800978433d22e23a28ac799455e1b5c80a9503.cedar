permit(
  principal,
  action in [Action::"6\u{1}\u{11}66"],
  resource
) when {
  ((true && ((ip(principal["r"])).isIpv6())) && false) && false
};
