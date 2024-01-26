permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (([false, Action::"action", true].containsAll([false, Action::"action", Action::"action"])) == [true, context, context])) && action
};
