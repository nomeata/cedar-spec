permit(
  principal,
  action == Action::"action",
  resource
) when {
  (true && ((ip("")).isLoopback())) && false
};
