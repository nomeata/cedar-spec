permit(
  principal in a::"\u{10}\0\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource
) when {
  true && context
};
