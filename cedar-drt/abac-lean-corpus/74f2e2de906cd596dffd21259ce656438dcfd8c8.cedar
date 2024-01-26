permit(
  principal,
  action in [Action::"action"],
  resource in a::"\u{10}"
) when {
  true && resource
};
