permit(
  principal is a in a::"66",
  action in [Action::"action"],
  resource is a in a::"66"
) when {
  (true && (if ((ip("")).isInRange(ip(""))) then (!(!false)) else ((ip("")).isIpv4()))) && (a::"66" in a::"")
};
