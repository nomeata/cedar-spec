permit(
  principal,
  action == Action::"action",
  resource
) when {
  (true && ((ip("87.255.255.255/4")).isIpv4())) && false
};
