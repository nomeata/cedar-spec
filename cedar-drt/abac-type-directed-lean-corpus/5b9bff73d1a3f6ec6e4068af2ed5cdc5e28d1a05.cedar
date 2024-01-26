permit(
  principal in a::"\te",
  action in [Action::"action"],
  resource == a::"6666\u{1}\0"
) when {
  true
};
