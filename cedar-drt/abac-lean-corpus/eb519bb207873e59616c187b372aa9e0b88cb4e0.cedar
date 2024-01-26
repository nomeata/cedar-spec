permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::"r"
) when {
  true && principal
};
