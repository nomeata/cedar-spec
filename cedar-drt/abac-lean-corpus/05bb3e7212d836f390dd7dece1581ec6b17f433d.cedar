permit(
  principal,
  action,
  resource == a::"jjjj\u{13}\r\0\0-\0"
) when {
  true
};
