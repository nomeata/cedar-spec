permit(
  principal,
  action in [Action::"action"],
  resource == a::"\0\0\u{8}"
) when {
  true
};
