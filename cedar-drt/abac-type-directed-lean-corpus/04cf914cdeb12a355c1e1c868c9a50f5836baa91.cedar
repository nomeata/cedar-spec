permit(
  principal is a in a::"&6",
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((if ((ip("54.36.38.0/")).isIpv4()) then a::"&6" else a::"&6") is a)
};
