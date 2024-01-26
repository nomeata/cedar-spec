permit(
  principal in a::"r\0\0\0\u{10}",
  action in [Action::"action"],
  resource == a::"r\0\0\0\u{10}"
) when {
  (true && (principal.containsAny(principal))) && principal
};
