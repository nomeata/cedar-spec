@im("u")
permit(
  principal,
  action in [Action::"action"],
  resource is a in a::"j\0\u{1}"
) when {
  true && [true, !false, !(!a::"")]
};
