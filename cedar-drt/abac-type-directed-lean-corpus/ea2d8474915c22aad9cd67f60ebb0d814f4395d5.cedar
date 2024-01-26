permit(
  principal,
  action in [Action::"action"],
  resource is a in a::"3"
) when {
  (true && ((ip("\u{1}\0\0E&\0\0\t")).isIpv4())) && false
};
