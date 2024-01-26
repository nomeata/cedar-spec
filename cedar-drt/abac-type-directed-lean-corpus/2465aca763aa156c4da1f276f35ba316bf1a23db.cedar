@m("")
forbid(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && ((ip(principal["z"])).isIpv4())) && ((ip(principal["z"])).isIpv4())) && false
};
