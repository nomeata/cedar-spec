permit(
  principal,
  action,
  resource == a::"~~"
) when {
  true && ([[] == "", false, false] == true)
};
