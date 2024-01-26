permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (([false, Action::"action", Action::"action"].containsAll([l::A::"", context])) == context)) && context
};
