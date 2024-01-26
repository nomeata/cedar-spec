forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::"jjj\0"
) when {
  (true && action) && principal
};
