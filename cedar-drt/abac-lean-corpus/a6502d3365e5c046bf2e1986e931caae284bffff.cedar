permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([false, context, false].contains(true)) == (!a::"j"))) && Action::"action"
};
