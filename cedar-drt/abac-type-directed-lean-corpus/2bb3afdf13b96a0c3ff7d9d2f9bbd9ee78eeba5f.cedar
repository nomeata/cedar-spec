forbid(
  principal == r323::"6",
  action in [Action::"action"],
  resource
) when {
  ((true && ((decimal(principal["B"])) == (decimal(principal["B"])))) && ((ip(principal["z"])).isIpv4())) && ((ip(principal["B"])).isIpv4())
};
