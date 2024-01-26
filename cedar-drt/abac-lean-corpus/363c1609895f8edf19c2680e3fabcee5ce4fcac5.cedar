permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && (principal has "")) && principal) && principal
};
