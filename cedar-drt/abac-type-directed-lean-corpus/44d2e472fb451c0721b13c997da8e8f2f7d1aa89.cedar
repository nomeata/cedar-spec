permit(
  principal is a in a::"666",
  action == Action::"action",
  resource is a in a::"666"
) when {
  true && (((ip("w\0")).isIpv4()) || true)
};
