permit(
  principal == a::"jjj",
  action in [Action::"action"],
  resource == a::"jjj"
) when {
  (true && Action::"action") && a::"jjj"
};
