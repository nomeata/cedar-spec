@Bsss("6333332v5z6666")
permit(
  principal is a in a::"66",
  action in [Action::"action"],
  resource is a in a::"66"
) when {
  true && ((Action::"action" in a::"66") || ((ip("666")).isIpv4()))
};
