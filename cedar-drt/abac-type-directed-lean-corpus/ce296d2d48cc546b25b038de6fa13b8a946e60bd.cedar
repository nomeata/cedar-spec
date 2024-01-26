permit(
  principal is B in r::"",
  action in [Action::"action"],
  resource
) when {
  (true && ((ip(principal["BssX"])).isLoopback())) && ((ip("54.54.54.160")).isIpv4())
};
