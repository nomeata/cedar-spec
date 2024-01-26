@A00000("")
permit(
  principal in a::"\u{c}",
  action in [Action::"action"],
  resource == a::"\u{c}"
) when {
  true && ((ip("\0\0\0\0\0\u{1}\0\0\0:\u{1e}\0\0\0\0\0:")) == principal)
};
