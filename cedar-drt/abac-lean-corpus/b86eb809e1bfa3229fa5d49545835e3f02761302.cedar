permit(
  principal is a,
  action == Action::"action",
  resource == a::"&\0jtm\u{10}\0\0\0\0\0\0\0pl"
) when {
  true && (principal.greaterThanOrEqual(!principal))
};
