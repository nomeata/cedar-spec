permit(
  principal == a::"",
  action,
  resource
) when {
  true && (16384 has "\0\0\u{2}ex")
};
