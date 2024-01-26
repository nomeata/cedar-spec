permit(
  principal in a::"66",
  action in [Action::"action"],
  resource is a in a::"66"
) when {
  (true && (a::"66" in [a::"66", resource])) && ((ip("\0\0\0")).isIpv4())
};
