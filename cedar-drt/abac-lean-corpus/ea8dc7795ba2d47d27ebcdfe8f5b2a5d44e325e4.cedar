permit(
  principal is a in a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  ((true && (principal has "")) && principal) && principal
};
