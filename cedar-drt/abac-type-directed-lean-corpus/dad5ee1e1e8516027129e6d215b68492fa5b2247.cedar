forbid(
  principal is a in a::"\u{1a}\u{1a}\u{1a}\u{18}\u{1a}666",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && (false || ((ip("")).isIpv4()))) && (a::"" has "")
};
