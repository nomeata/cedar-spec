permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((if false then (if false then (ip("0.0.54.164")) else (ip("0.0.0.0"))) else (ip("0.0.0.0"))).isIpv4())) && false
};
