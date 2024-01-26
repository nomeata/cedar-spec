permit(
  principal,
  action,
  resource is p in z::""
) when {
  (true && ((ip(principal["Bsss"])).isIpv4())) && ((ip("")).isIpv4())
};
