forbid(
  principal in xvptqs::"",
  action in [Action::"n66666666"],
  resource is xvptqs in xvptqs::""
) when {
  (true && ((ip(principal["A"])).isIpv4())) && false
};
