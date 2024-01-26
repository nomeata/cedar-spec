permit(
  principal,
  action,
  resource is a in a::""
) when {
  (true && ((ip("")).isIpv4())) && false
};
