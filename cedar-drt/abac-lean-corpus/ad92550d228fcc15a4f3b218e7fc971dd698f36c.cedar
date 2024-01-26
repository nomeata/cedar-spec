permit(
  principal == a::"G\0\0\0\u{2}\0\0",
  action in [Action::"action"],
  resource == a::"G\0\0\0\u{2}\0\0"
) when {
  true
};
