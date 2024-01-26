permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([false, context, "xj"].containsAll([a::"j", a::"", a::"", false, a::"", "", principal])) == principal)) && principal
};
