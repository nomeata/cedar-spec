permit(
  principal,
  action,
  resource
) when {
  (true && ((a::"6" in Action::"action") || ((ip("")).isIpv4()))) && false
};
