@A("\0\u{8}at|")
forbid(
  principal,
  action,
  resource
) when {
  true && principal
};
