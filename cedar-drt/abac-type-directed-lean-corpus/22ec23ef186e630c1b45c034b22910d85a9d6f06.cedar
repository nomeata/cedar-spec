forbid(
  principal is a in a::"\u{1}/6",
  action in [Action::"action"],
  resource is a in a::"\u{1}/6"
) when {
  ((true && ((a::"\u{1}/6" is a) == (principal is a))) && (resource is a)) && ((ip("")).isIpv6())
};
