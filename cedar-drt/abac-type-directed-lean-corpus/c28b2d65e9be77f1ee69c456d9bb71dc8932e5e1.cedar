forbid(
  principal == a::"6",
  action in [Action::"action"],
  resource
) when {
  ((true && ((if ((ip("255.255.255.255/0")).isIpv4()) then [false, true, true] else [true, true, true]) == [(ip("1313:1313:1313:1313:1313:13c6:1336:362a/0")).isIpv6(), false, false])) && false) && false
};
