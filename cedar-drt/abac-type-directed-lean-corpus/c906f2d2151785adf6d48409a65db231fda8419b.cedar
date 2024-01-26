forbid(
  principal is a in a::"\u{4}\u{4}\u{1}",
  action in [Action::"action"],
  resource == a::"\u{4}\u{4}\u{1}"
) when {
  true
};
