permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([false, context, false].contains([false, context, false])) == true)) && (!a::"j")
};
