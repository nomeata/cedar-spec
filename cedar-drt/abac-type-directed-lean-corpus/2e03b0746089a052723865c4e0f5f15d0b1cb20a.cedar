permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && ((ip("1128.54.54.0")).isIpv4())) && false
};
