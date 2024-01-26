permit(
  principal == a::"r\0\0\0",
  action in [Action::"action"],
  resource in a::""
) when {
  true && a::""
};
