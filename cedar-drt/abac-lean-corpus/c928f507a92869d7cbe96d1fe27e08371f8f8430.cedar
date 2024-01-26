permit(
  principal is a,
  action in [Action::"action"],
  resource in a::""
) when {
  (true && A::"") && principal
};
