permit(
  principal is a in a::"\06",
  action in [Action::"action"],
  resource is a in a::"\06"
) when {
  (true && ((ip("")).isIpv6())) && true
};
