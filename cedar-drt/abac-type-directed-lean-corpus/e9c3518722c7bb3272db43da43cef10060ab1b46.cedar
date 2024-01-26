permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((if ((ip("54.160.ù4.0")).isIpv4()) then action else action) is a)
};
