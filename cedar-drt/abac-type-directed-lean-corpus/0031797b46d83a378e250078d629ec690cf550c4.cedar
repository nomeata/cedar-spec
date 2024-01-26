@B("666\0\0\0")
permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((if (principal has "Z633") then (if false then (ip("51.54.54.9/19")) else (ip("54.199.255.54/11"))) else (ip("0.0.0.0"))).isIpv4())) && false
};
