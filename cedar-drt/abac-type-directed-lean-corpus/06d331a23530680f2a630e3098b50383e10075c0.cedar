permit(
  principal,
  action in [Action::"action"],
  resource == M::""
) when {
  (true && ((ip("6\0\0\0-")).isIpv4())) && (M::"" has "z")
};
