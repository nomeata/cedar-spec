forbid(
  principal == a::"jjjj\u{13}\r",
  action in [Action::"action"],
  resource
) when {
  true
};
