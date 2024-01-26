@m("")
forbid(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && ((ip(principal["Bsss"])).isIpv4())) && ((ip(principal["Bsss"])).isIpv4())) && ((if false then (if false then (ip("51.204.54..0/21")) else (ip("0.0.54.54"))) else (ip("0.0.0.0"))).isIpv4())
};
