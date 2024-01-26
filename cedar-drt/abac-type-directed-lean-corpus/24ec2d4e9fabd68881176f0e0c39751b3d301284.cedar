@tMss("6")
permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && ((if ((ip("0:32:3600:36a0:3636:a435:3636:21ff")) == (ip("0.0.0.0"))) then (ip("0.0.0.0")) else (ip("0.0.0.0"))).isIpv4())) && false
};
