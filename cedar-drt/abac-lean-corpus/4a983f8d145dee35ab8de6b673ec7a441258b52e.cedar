permit(
  principal == a::"l\u{1}\u{3}onstraint\0jbjjjjjjj0%\0",
  action,
  resource == a::"l\u{1}\u{3}onstraint\0jbjjjjjjj0%\0"
) when {
  true && ([Action::"action", action] is a)
};
