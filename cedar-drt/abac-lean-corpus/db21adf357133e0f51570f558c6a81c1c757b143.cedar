permit(
  principal is a in a::"\u{10}\0\0",
  action in [Action::"action"],
  resource == a::"\u{10}\0\0"
) when {
  true && (!context)
};
