permit(
  principal == a::"~j",
  action in [Action::"action"],
  resource == a::"~j"
) when {
  (true && (([false, Action::"action", Action::"action"].containsAll(Action::"action")) == context)) && Action::"action"
};
