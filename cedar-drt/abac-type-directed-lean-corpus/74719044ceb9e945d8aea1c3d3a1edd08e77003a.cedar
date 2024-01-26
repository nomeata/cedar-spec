@lyyyyyyWss_s("")
permit(
  principal is a in a::"6",
  action == Action::"action",
  resource is a in a::"6"
) when {
  (true && ((if ((ip("99.97.0.1/1")).isLoopback()) then (ip("0.0.0.0")) else (ip("0.0.0.0"))).isLoopback())) && false
};
