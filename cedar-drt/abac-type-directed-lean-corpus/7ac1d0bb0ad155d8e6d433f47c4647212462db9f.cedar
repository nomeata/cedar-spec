permit(
  principal == a::"666\u{18}\0\0\0\0\0\0\0\t\t",
  action in [Action::"action"],
  resource == a::"666\u{18}\0\0\0\0\0\0\0\t\t"
) when {
  true
};
