permit(
  principal,
  action,
  resource is a in a::""
) when {
  true && ((ip(principal["A"])).isIpv4())
};
