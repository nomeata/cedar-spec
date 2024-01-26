forbid(
  principal == a::"36",
  action in [Action::"action"],
  resource
) when {
  ((true && ([ip("0.1.51.236"), ip("0.0.0.0"), ip("0.0.0.0")] == [])) && false) && false
};
