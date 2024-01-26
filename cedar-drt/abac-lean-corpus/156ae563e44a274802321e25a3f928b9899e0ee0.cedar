permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([true, Action::"action", false].containsAll(Action::"action" in a::"")) == Action::"action")) && context
};
