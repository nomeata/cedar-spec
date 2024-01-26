permit(
  principal == a::"66",
  action,
  resource is a in a::"66"
) when {
  (true && ((ip("")).isIpv6())) && ((ip("")).isIpv6())
};
