forbid(
  principal,
  action == Action::"",
  resource
) when {
  (true && ((ip(principal["r"])).isIpv4())) && false
};
