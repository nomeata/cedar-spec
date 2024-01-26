permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && a::"\u{10}\0\0") && Action::"action") && a::"\u{10}\0\0"
};
