@G("")
permit(
  principal,
  action,
  resource == a::"z"
) when {
  (true && r::r::r::"zj\0\0\0\u{1}\0\0\0\0") && principal
};
