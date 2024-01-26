permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([false, Action::"action", Action::"action"].containsAll([])) == (if principal then principal else principal))) && principal
};
