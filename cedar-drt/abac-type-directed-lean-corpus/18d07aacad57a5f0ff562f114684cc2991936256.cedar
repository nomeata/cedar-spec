permit(
  principal == a::"6\u{1}\0\0",
  action in [Action::"action"],
  resource is a
) when {
  ((true && (if ((ip("")).isIpv4()) then false else false)) && true) && false
};
