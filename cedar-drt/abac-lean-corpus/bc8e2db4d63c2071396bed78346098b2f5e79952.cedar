permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && ((action is a) == A000000000::"")) && principal
};
