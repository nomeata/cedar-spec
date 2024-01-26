forbid(
  principal,
  action == Action::"6\u{1}\u{11}66",
  resource
) when {
  (true && ((ip(principal["r"])).isIpv4())) && false
};
