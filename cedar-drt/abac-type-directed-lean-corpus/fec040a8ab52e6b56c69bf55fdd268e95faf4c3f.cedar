permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && ((ip(action["P"])).isIpv4())) && ((ip(action["P"])).isIpv4())
};
