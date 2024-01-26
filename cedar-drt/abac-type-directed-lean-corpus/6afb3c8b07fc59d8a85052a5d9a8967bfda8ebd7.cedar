forbid(
  principal,
  action in [Action::"action"],
  resource == a::"t"
) when {
  (true && ((ip("\0\0")).isLoopback())) && false
};
