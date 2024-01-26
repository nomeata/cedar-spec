permit(
  principal == a::"\0\0\0\t6",
  action == Action::"action",
  resource is a in a::"\0\0\0\t6"
) when {
  true && ((ip("\'")).isIpv4())
};
