permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([true, context, false].contains(true)) == (!Action::"action"))) && (if principal then principal else principal)
};
