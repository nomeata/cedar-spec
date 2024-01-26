permit(
  principal in a::"\u{10}\0[d",
  action in [Action::"action"],
  resource
) when {
  ((true && [a::"\u{10}\0[d", principal, "", principal * 0]) && principal) && principal
};
