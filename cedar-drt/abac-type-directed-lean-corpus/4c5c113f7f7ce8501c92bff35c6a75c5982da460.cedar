permit(
  principal == m::r::"",
  action == m::Action::"action",
  resource is m::r in m::A00000::""
) when {
  (true && ((ip(action["n333333stl9bbe"])).isIpv4())) && ((ip(principal["n333333stl9bbe"])).isIpv4())
};
