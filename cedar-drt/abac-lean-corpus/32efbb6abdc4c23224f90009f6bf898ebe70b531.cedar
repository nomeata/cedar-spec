permit(
  principal == a::"\0\0\u{8}",
  action in [Action::"action"],
  resource is a in a::"\0\0\u{8}"
) when {
  true && (((1953184666628070144 == true).isInRange(a::"\0\0\u{8}")) == true)
};
