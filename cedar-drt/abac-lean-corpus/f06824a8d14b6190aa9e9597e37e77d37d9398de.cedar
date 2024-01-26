permit(
  principal in a::"&\u{10}\u{c}",
  action in [Action::"action"],
  resource == a::"&\u{10}\u{c}"
) when {
  true && ((ip("\0\0\0\0\0\0\0D\u{1e}\u{1e}\0\0\0\0\0:\0\0")) == false)
};
