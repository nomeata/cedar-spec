permit(
  principal in a::"\u{8}",
  action in [Action::"action"],
  resource is a in a::"\u{8}"
) when {
  true && ((action.lessThanOrEqual("\0\0\0jjjj:jjj\0\0j/\0")) == (a::"\u{8}" in principal))
};
