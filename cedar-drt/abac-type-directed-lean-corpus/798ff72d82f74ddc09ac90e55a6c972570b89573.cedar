permit(
  principal is a in a::"z6666",
  action in [Action::"action"],
  resource is a in a::"z6666"
) when {
  true && ((Action::"action" in a::"z6666") || ((ip("666")).isIpv4()))
};
