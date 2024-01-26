permit(
  principal in a::"\0\0\u{8}",
  action in [Action::"action"],
  resource == a::"\0\0\u{8}"
) when {
  true && ((ip(principal)) == context)
};
