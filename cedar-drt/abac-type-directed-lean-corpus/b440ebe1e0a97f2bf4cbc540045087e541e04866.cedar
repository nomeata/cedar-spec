@A("")
@nJJJJJJJJJ("")
forbid(
  principal,
  action in [Action::"sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss66"],
  resource
) when {
  (true && ((ip(resource["r03"])).isIpv4())) && ((decimal(principal["r"])).greaterThan(decimal("")))
};
