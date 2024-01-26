permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a
) when {
  ((true && (if ((ip("")).isIpv4()) then false else false)) && true) && false
};
