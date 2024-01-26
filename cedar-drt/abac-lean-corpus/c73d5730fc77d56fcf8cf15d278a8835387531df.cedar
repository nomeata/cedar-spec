permit(
  principal == a::"\r\0",
  action == Action::"action",
  resource == a::""
) when {
  true && principal
};
