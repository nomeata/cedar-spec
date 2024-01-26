permit(
  principal in a::"j\0\0\0\0",
  action in [Action::"action"],
  resource == a::"j\0\0\0\0"
) when {
  (true && ((false == (!context)).containsAny(action))) && Action::"action"
};
