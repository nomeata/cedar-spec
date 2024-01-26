permit(
  principal in a::"\u{10}\0\0dataj",
  action in [Action::"action"],
  resource
) when {
  true && Action::"action"
};
