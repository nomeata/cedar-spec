permit(
  principal is a,
  action == Action::"action",
  resource == a::"&\0j\0u\u{10}\0"
) when {
  true && (false.greaterThanOrEqual(principal))
};
