permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([true, Action::"action", false].containsAll(principal in a::"j")) == principal)) && principal
};
