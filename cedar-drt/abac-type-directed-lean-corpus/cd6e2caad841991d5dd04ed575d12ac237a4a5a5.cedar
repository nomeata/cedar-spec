forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  true && ((if ((ip("54.54.89.89")).isMulticast()) then (ip("6")) else (ip(""))).isIpv4())
};
