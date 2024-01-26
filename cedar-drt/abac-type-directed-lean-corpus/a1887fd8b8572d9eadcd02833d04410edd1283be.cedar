permit(
  principal,
  action,
  resource
) when {
  true && ((ip("")).isIpv6())
};
