@JrpYgl000("")
@S("")
@m("")
forbid(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && ((ip(principal["r"])).isIpv4())) && ((ip(principal["r"])).isIpv4())) && false
};
