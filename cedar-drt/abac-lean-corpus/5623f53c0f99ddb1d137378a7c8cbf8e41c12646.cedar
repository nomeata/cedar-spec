permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && ([] || a::"\u{10}")
};
