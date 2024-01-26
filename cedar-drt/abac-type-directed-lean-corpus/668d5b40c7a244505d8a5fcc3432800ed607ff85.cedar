@B("\0\0\0")
@S("")
@m("")
forbid(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && ((ip(principal["A"])).isIpv4())) && ((ip(principal["A"])).isIpv4())) && false
};
