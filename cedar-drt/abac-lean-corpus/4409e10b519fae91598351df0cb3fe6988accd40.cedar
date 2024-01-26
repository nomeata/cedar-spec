permit(
  principal == a::"0bjjj",
  action in [Action::"action"],
  resource == a::"0bjjj"
) when {
  (true && (([false, Action::"action", Action::"action"].containsAll([a::"", context, false])) == (!a::"0bjjj"))) && (!false)
};
