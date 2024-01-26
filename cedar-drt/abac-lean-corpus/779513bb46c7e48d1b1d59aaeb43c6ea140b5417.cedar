permit(
  principal == a::"&jj\0\0\0",
  action in [Action::"action",Action::"action"],
  resource == a::"jjj"
) when {
  (true && Action::"action") && a::"jjj"
};
