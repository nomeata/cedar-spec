forbid(
  principal == a::"66666",
  action in [Action::"action"],
  resource
) when {
  ((true && ((if ((ip("54.54.54.24Â")).isIpv4()) then 62188 else 0) == 0)) && false) && false
};
