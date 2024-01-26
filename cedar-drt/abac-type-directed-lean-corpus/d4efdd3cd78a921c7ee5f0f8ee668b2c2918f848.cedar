permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a
) when {
  ((true && (if ((ip("")).isIpv4()) then false else ((ip("&5\0")).isIpv4()))) && true) && true
};
