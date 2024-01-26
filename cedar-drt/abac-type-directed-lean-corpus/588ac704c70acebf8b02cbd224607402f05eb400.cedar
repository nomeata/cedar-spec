permit(
  principal == a::"\0\0\0\0)\0\0\0\0\0\0\0\u{1}&666\u{e}\0\0\0\0)\0\0\0",
  action in [Action::"action"],
  resource == a::"\0\0\0\0)\0\0\0\0\0\0\0\u{1}&666\u{e}\0\0\0\0)\0\0\0"
) when {
  true
};
