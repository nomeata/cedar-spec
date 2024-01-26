permit(
  principal is a,
  action in [Action::"action"],
  resource == a::"\u{10}\0[d"
) when {
  false && principal
};
