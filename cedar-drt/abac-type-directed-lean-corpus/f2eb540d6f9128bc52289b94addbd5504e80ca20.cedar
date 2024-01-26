permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((if ((decimal("0.1")) == (decimal("0.1"))) then (ip("::ffff:255.255.255.255")) else (ip("0.0.0.0"))).isMulticast())) && false
};
