permit(
  principal == a::"jjjj",
  action in [Action::"action"],
  resource
) when {
  true && a::""
};
