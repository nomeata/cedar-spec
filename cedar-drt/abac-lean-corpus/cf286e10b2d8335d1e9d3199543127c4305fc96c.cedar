permit(
  principal == a::"j",
  action in [Action::"action"],
  resource is a
) when {
  (true && (([false, principal, true].contains(context)) == a::"")) && Action::"action"
};
