permit(
  principal == a::"p\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0r_kj\u{16}",
  action,
  resource
) when {
  ((true && (((a::"p\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0r_kj\u{16}" in A::"") in a::"p\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0r_kj\u{16}") in principal)) && principal) && principal
};
