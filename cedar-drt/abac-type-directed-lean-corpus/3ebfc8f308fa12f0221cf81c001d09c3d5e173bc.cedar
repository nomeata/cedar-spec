permit(
  principal == a::"#\0\0\u{1}\u{11}",
  action,
  resource is a in a::"#\0\0\u{1}\u{11}"
) when {
  false
};
