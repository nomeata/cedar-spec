@r("\u{1}\0")
permit(
  principal,
  action,
  resource == a::"jjj\n"
) when {
  true
};
