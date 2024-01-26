forbid(
  principal == a::"3",
  action in [Action::"action"],
  resource is a in a::"3"
) when {
  (true && ((ip("\0\0E&action_constr")).isIpv4())) && true
};
