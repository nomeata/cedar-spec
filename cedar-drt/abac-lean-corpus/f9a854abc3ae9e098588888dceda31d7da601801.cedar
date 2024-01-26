permit(
  principal,
  action in [Action::"action"],
  resource in a::"\u{10}\0\0"
) when {
  true && resource
};
