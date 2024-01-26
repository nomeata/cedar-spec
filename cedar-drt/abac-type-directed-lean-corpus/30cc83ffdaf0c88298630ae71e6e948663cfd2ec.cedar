permit(
  principal is a in a::"\0\u{16}",
  action in [Action::"action"],
  resource is a in a::"\0\u{16}"
) when {
  (true && ((ip("")).isIpv4())) && true
};
