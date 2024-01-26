permit(
  principal is a in a::"&6",
  action in [Action::"action"],
  resource is a in a::"&6"
) when {
  true && ((if ((ip("160.54..38.0")).isIpv4()) then a::"&6" else resource) is a)
};
