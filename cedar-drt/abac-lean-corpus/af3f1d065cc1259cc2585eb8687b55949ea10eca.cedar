permit(
  principal == a::"AhhN0bjjj",
  action in [Action::"action"],
  resource == a::"AhhN0bjjj"
) when {
  (true && (([false, Action::"action", Action::"action"].containsAll([a::"", context, false])) == (!Action::"action"))) && (!a::"")
};
