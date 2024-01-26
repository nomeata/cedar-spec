permit(
  principal in a::"v26z6",
  action == Action::"action",
  resource in a::""
) when {
  (true && ((ip("")).isIpv4())) && (principal has "d")
};
