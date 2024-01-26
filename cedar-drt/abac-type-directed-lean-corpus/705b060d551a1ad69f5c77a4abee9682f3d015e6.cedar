permit(
  principal,
  action == Action::"action",
  resource is a in a::""
) when {
  true && ((ip(".0.0.0/11")).isInRange(ip("0.0.0.0")))
};
