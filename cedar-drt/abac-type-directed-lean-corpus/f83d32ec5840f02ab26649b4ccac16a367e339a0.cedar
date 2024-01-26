permit(
  principal is a in a::"&6",
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((if ((ip("54.36.38.0/221")).isIpv4()) then action else action) is a)
};
