permit(
  principal is a in a::"&6",
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((if ((ip("2600:3636:647a:ef36:3636:40cb:3636:3640")).isInRange(ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"))) then resource else resource) is a)
};
