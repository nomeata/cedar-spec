permit(
  principal == a::"jj",
  action in [Action::"action"],
  resource == a::"jj"
) when {
  (true && (([true, Action::"action", 7672862160438655867].containsAll(context)) == a::"")) && a::""
};
