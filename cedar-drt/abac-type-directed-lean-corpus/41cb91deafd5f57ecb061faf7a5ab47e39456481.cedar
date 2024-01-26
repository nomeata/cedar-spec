@hu3333Ya("5-")
permit(
  principal,
  action,
  resource == a::"666\u{1}\0\0\0666"
) when {
  true && (a::"" has "")
};
