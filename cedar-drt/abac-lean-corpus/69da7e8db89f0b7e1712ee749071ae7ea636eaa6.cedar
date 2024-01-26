permit(
  principal == a::"i",
  action in [Action::"action"],
  resource == a::"i"
) when {
  true && a::"i"
};
