permit(
  principal == a::"&\u{10}\u{c}",
  action in [Action::"action"],
  resource == a::"&\u{10}\u{c}"
) when {
  true && ((ip("\0\0\0non_head/_constraints\0")) == principal)
};
