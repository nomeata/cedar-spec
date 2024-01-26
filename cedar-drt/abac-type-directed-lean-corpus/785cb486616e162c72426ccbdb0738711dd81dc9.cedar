permit(
  principal in B::r::"",
  action in [B::Action::"action"],
  resource is B::A in B::r::""
) when {
  (true && ((ip(principal["r"])).isLoopback())) && ((ip("\0\u{2}")).isIpv4())
};
