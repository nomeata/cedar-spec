permit(
  principal is B::A in B::r::"",
  action in [B::Action::"action"],
  resource is B::r in B::r::""
) when {
  (true && ((ip(principal["r333T7"])).isIpv4())) && ((decimal(principal["r"])).lessThanOrEqual(decimal("")))
};
