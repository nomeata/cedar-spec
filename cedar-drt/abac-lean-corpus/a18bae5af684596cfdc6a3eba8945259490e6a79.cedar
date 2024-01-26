permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([false, context, "xj"].containsAll(["", Action::"action"])) == true)) && Action::"action"
};
