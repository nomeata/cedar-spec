permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([true, Action::"action", context].contains(false)) == principal)) && principal
};
