forbid(
  principal is a in a::"3\u{1}",
  action in [Action::"action",Action::"action"],
  resource is a in a::"3\u{1}"
) when {
  (true && ((if true then (ip(":")) else (if true then (ip("38.54.0.0")) else (ip("0.0.55.255")))).isIpv4())) && (!false)
};
