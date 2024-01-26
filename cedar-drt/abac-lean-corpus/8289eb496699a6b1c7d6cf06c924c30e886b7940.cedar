permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([false, principal, action].containsAll(context)) == a::"j")) && principal
};
