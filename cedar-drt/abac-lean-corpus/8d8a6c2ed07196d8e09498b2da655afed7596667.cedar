permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([true, Action::"action", false].contains(a::"" in a::"j")) == principal)) && principal
};
