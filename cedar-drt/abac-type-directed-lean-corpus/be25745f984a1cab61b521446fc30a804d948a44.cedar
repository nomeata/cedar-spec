forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a
) when {
  (true && ((ip(if false then "" else "")).isIpv4())) && true
};
