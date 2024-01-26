forbid(
  principal,
  action in [Action::"action"],
  resource is a in a::"6"
) when {
  (true && ((ip("54.255.255.255")).isLoopback())) && false
};
