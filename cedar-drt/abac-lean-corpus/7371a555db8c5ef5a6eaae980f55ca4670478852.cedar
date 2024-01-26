permit(
  principal == _gAh::"j",
  action in [Action::"action"],
  resource == _gAh::"j"
) when {
  (true && principal) && principal
};
