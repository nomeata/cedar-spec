permit(
  principal,
  action,
  resource == a::"i\0\0\u{16}"
) when {
  (true && resource) && principal
};
