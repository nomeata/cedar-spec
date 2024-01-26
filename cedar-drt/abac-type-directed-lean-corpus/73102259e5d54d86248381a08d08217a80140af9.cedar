permit(
  principal == a::"23\0\u{1}",
  action,
  resource is a in a::"23\0\u{1}"
) when {
  true && ([].contains(true))
};
