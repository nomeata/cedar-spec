permit(
  principal == a::"jjjj\u{13}\r\0\0-\0\u{10}\0\0\0\0\0",
  action in [Action::"action"],
  resource
) when {
  true && "\u{19}"
};
