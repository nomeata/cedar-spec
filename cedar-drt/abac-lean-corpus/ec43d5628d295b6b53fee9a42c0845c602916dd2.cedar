permit(
  principal == a::"\0\0\0jjj\0\0\0\u{7f}\0\0",
  action in [Action::"action"],
  resource == a::"\0\0\0jjj\0\0\0\u{7f}\0\0"
) when {
  true && resource
};
