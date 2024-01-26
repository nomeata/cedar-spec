forbid(
  principal == a::"jjj\0",
  action == Action::"action",
  resource == a::""
) when {
  (true && principal) && principal
};
