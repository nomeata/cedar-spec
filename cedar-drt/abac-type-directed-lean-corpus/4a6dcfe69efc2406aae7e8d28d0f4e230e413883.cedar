permit(
  principal == a::"6.",
  action == Action::"action",
  resource is a in a::"6."
) when {
  (true && (((ip(".0.0.0/11")).isInRange(ip("0.0.0.0"))) || false)) && false
};
