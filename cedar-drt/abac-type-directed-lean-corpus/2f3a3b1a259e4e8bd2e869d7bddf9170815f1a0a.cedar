forbid(
  principal == a::"\0\0\026\u{1}",
  action in [Action::"action"],
  resource == a::"\0\0\026\u{1}"
) when {
  true
};
