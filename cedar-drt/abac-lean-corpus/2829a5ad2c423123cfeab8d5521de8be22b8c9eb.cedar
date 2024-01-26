@A00000("")
permit(
  principal in a::"\0\0v\u{c}",
  action in [Action::"action"],
  resource == a::"\0\0v\u{c}"
) when {
  true && ((ip("\0\0\0\0\0\u{1}\0D\u{1e}\u{1e}/\0\0\0\0\0:")) == principal)
};
