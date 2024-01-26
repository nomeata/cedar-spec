permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([true, Action::"action", a::"j"].contains(context)) == (!resource))) && (!principal)
};
