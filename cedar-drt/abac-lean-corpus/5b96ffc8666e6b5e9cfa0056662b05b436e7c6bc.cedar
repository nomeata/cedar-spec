permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::"j"
) when {
  true && principal
};
