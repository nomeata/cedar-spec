permit(
  principal == a::"\0\0\0\0\0\0\0\0\0\0\u{1c}",
  action in [Action::"action"],
  resource == a::"\0\0\0\0\0\0\0\0\0\0\u{1c}"
) when {
  (true && principal) && action
};
