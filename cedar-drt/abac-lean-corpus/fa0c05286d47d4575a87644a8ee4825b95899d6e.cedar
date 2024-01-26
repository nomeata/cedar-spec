permit(
  principal == a::"jtemjjjjj",
  action in [Action::"action"],
  resource == a::"jtemjjjjj"
) when {
  (true && (([false, a::"", Action::"action"].containsAll([A::"\0\0\0\0\0", context])) == false)) && principal
};
