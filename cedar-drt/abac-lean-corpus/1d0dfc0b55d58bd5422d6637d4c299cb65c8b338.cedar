forbid(
  principal == a::"@\0\0\0jjjjjjjjjhjj\0\0\0\0k\\\\\\\0\0\0\0\0\0\0\0\u{4}\u{2}\0\0&\0",
  action in [Action::"action"],
  resource
) when {
  (true && (A::"" in principal)) && principal
};
