permit(
  principal is a in a::"\n6",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && ((ip(action["P"])).isIpv4())) && ((ip(principal["P"])).isIpv4())
};
