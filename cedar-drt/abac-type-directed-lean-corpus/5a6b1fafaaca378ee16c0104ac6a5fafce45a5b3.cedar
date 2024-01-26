permit(
  principal is a in a::"333",
  action == Action::"action",
  resource is a
) when {
  (true && ((ip("662%:")).isIpv4())) && (((ip("\0\03333")).isIpv4()) && (principal is a))
};
