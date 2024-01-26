forbid(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  ((true && (((ip("0.0.0.0/11")).isInRange(ip("0.0.0.0"))) || false)) && false) && false
};
