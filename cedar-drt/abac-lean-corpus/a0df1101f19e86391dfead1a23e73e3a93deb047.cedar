permit(
  principal in a::"\0\0\u{c}",
  action in [Action::"action"],
  resource == a::"\0\0\u{c}"
) when {
  true && ((ip(context)) == a::"\0\0\u{c}")
};
