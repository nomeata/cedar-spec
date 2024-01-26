permit(
  principal == a::"",
  action,
  resource is a in a::""
) when {
  (true && ((if true then (if true then (ip("50ff:ff36:3636:3636:5ccff:f6ff")) else (ip("::ff:ff00:cb00:ffff:36ff"))) else (ip("0.0.0.0"))).isIpv4())) && false
};
