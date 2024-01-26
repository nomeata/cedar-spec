forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource is a in a::""
) when {
  (true && ((ip("4.54.160.54/21")).isLoopback())) && false
};
