permit(
  principal is a in a::"&6",
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((if ((ip("54.36.38.0/ù")).isIpv4()) then resource else (if false then principal else principal)) is a)
};
