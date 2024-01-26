permit(
  principal == a::"tm\u{10}\0\0\0\0\0\0\0pl",
  action == Action::"action",
  resource == a::"tm\u{10}\0\0\0\0\0\0\0pl"
) when {
  true && (principal.greaterThanOrEqual(principal))
};
