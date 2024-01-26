forbid(
  principal is a in a::"\u{1}\0\0\0",
  action in [Action::"action"],
  resource is a in a::"\u{1}\0\0\0"
) when {
  (true && ((ip("6$666")).isIpv4())) && (action has "")
};
