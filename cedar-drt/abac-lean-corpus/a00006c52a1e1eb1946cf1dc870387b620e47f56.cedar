permit(
  principal,
  action in [],
  resource == a::"p\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0r_kj\u{16}"
) when {
  (true && principal) && action
};
