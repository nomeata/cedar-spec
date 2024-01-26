permit(
  principal is a in a::"35",
  action in [Action::"action"],
  resource is a in a::"35"
) when {
  (true && ((ip("666")).isIpv4())) && (false == false)
};
