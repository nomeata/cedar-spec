@ksss("")
permit(
  principal,
  action,
  resource is a in a::"66R"
) when {
  true && (a::"66R" has "\0\0\0")
};
