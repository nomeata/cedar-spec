permit(
  principal,
  action == Action::"action",
  resource
) when {
  true && ((ip("156.156.156.156")).isIpv4())
};
