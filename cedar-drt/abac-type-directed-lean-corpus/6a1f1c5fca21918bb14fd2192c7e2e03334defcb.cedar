@r("MM")
forbid(
  principal == a::"6",
  action in [Action::"action"],
  resource is a in a::"6"
) when {
  (true && ((ip(principal["Z333"])).isIpv4())) && ((ip("")).isIpv4())
};
