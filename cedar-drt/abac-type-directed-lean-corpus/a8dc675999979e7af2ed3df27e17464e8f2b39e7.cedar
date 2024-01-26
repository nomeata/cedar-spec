permit(
  principal is a in a::":6\0\u{11}\0\03333",
  action == Action::"action",
  resource is a
) when {
  (true && ((ip("662%:6\0\u{11}\0\06666")).isIpv4())) && false
};
