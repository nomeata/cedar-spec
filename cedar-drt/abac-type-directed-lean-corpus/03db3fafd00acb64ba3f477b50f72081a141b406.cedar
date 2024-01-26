permit(
  principal == a::"2!3\0\u{1}",
  action,
  resource is a in a::"2!3\0\u{1}"
) when {
  true && ([[].containsAny([])].contains((decimal("d111111111")) == (decimal("11111111111"))))
};
