permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  true && a::"\u{10}\0\0"
};
