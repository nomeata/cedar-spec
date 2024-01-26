@A("\0\0\0\0")
permit(
  principal in a::"\u{c}\0\u{5}\0",
  action in [Action::"action"],
  resource == a::"\u{c}\0\u{5}\0"
) when {
  true && ((ip("\0\0\0\0\0\u{1}\0\0\0:\u{1e}\0\0\0\0\0:")) == principal)
};
