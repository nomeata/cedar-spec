permit(
  principal is a in a::"6",
  action == Action::"action",
  resource is a in a::"6"
) when {
  (true && ((ip("")).isIpv4())) && true
};
