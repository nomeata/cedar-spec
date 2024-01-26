permit(
  principal is a in a::"\u{8}",
  action == Action::"action",
  resource is a in a::"\u{8}"
) when {
  true && ((false.lessThanOrEqual(context)) == a::"\u{8}")
};
