forbid(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  ((true && ((if principal then principal else principal) in principal)) && principal) && principal
};
