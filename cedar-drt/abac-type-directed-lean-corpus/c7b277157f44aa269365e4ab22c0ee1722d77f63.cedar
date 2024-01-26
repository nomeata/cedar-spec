forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && ((if ((ip("0.0.51.54")) == (ip("0.0.0.0"))) then (decimal("0.0")) else (decimal("0.0"))) == (decimal("0.0")))) && false
};
