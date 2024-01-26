forbid(
  principal is a in a::"\0\0\u{2}:",
  action in [Action::"action"],
  resource == a::"\0\0\u{2}:"
) when {
  (true && ((if (!(9223372036854775807 < 9223372036854775807)) then (ip("                                ")) else (ip(" f\0\0\0\t"))).isLoopback())) && true
};
