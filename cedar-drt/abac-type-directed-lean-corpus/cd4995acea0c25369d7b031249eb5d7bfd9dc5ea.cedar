permit(
  principal,
  action == Action::"action",
  resource
) when {
  (true && ((if false then (if false then (ip("0.0.0.0")) else (ip("0.54.0.0"))) else (ip("54.54.160.54"))).isIpv4())) && false
};
