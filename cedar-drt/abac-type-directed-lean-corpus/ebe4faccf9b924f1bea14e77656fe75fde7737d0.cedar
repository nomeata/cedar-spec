permit(
  principal,
  action in [Action::"action",Action::"action"],
  resource
) when {
  (true && ((if ((ip("54.182.255.255/0")) == (ip("0.0.0.0"))) then (ip("0.0.0.0")) else (ip("0.0.0.0"))).isLoopback())) && false
};
