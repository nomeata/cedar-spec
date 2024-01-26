permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ((if false then (if false then (ip("::ffff:255.255.255.255")) else (ip("::f2"))) else (ip("0.0.0.0"))).isInRange(ip("0.0.0.0")))) && false) && false
};
