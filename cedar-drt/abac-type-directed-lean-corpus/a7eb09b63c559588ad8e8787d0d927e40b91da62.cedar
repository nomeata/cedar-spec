permit(
  principal == B::r::"",
  action == B::Action::"action",
  resource is B::r in B::A::""
) when {
  (true && ((decimal(principal["xv033333stl933"])).lessThan(decimal(principal["r"])))) && ((ip(principal["r"])).isIpv6())
};
