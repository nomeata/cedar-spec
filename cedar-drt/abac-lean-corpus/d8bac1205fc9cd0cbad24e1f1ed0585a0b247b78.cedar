permit(
  principal == a::"r\0\0\0",
  action in [Action::"action"],
  resource == a::"r\0\0\0"
) when {
  ((true && context) && principal) && principal
};
