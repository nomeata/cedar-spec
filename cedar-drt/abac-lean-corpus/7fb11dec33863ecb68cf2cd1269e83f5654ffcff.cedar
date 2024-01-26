permit(
  principal in a::"\u{8}",
  action in [Action::"action"],
  resource is a in a::"\u{8}"
) when {
  true && ((context.lessThanOrEqual(a::"\u{8}")) == a::"\u{8}")
};
