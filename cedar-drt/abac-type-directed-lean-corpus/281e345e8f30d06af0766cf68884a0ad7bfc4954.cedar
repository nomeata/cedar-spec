permit(
  principal is B::C in B::r::"",
  action in [B::Action::"action",B::Action::"action",B::Action::"action"],
  resource is B::A in B::r::""
) when {
  (true && ((ip(principal["r"])).isLoopback())) && false
};
