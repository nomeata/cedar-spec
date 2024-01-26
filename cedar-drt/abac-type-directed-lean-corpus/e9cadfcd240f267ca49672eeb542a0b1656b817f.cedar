permit(
  principal is a in a::"7",
  action in [Action::"action"],
  resource == a::"7"
) when {
  ((true && ((!((ip("e1e1:e1e1:e1e1:e1e1:e1e1:e1e1:e1e1:e5e1/96")).isIpv4())) == false)) && true) && true
};
