forbid(
  principal is a,
  action in [Action::"action"],
  resource
) when {
  ((true && a::"\u{1}") && principal) && principal
};
