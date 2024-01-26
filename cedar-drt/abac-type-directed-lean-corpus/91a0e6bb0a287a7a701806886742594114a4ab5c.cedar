forbid(
  principal == a::"6",
  action == Action::"action",
  resource == a::"6"
) when {
  false && ((ip("::ffc9:9:4069")).isLoopback())
};
