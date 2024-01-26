permit(
  principal == a::"\0\u{1b}|&6666.66\0\u{1b}",
  action == Action::"action",
  resource is a in a::"\0\u{1b}|&6666.66\0\u{1b}"
) when {
  true && ((ip("\0\0\0\t66666ances\u{1}")).isInRange(ip("")))
};
