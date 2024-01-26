forbid(
  principal == a::"",
  action == Action::"action",
  resource is a in a::""
) when {
  false && ((ip("")).isIpv4())
};
