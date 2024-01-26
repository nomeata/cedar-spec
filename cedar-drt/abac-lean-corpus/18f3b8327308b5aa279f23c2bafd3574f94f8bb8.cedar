permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([true, context, a::""].contains(a::"")) == a::"j")) && false
};
