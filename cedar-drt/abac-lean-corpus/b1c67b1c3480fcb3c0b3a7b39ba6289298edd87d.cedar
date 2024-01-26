permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([true, Action::"action", a::""].contains(a::"")) == Action::"action")) && action
};
