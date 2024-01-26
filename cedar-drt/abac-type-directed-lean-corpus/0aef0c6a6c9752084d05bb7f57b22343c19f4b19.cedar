permit(
  principal == a::"6&\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource is a in a::"6&\0"
) when {
  true && ((ip("3")).isLoopback())
};
