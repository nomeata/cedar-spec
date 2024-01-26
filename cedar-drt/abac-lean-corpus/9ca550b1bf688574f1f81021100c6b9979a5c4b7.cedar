permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([].contains(principal)) == context)) && a::"j"
};
