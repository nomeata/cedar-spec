permit(
  principal == a::"\u{8}",
  action in [Action::""],
  resource == a::"\u{8}"
) when {
  true && ((principal.isIpv6()) == principal)
};
