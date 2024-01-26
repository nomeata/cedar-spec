permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && a::"") && principal) && principal
};
