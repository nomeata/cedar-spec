@m("")
forbid(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && ((ip(principal["B"])).isIpv4())) && ((ip(principal["B"])).isIpv4())) && false
};
