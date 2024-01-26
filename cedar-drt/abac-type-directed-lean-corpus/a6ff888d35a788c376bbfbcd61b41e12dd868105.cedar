permit(
  principal is a in a::"t6\0A",
  action in [Action::"action"],
  resource == a::""
) when {
  false && ((if false then (if false then (ip("0.0.0.0")) else (ip("0.0.0.0"))) else (if false then (ip("0.0.0.0")) else (ip("0.0.0.0")))).isInRange(ip("0.0.0.0")))
};
