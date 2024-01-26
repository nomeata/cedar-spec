permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (([false, Action::"action", Action::"action"].containsAll([Action::"action", context, action])) == (!principal))) && principal
};
