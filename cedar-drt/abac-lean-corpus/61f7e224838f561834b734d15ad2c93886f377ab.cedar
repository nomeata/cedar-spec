permit(
  principal == a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0jhgj",
  action in [Action::"action"],
  resource
) when {
  ((true && Action::"action") && false) && a::""
};
