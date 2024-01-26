permit(
  principal == a::"i\0\u{5}",
  action == Action::"action",
  resource == a::"i\0\u{5}"
) when {
  (true && resource) && false
};
