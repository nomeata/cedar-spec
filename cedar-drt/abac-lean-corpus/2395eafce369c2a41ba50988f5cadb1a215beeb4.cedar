forbid(
  principal == a::"jj",
  action in [Action::"action"],
  resource == a::"jj"
) when {
  (true && (([false, Action::"action", Action::"action"].containsAll([Action::"action", context, principal])) == action)) && Action::"action"
};
