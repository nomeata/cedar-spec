permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && action) && (principal == a::"R")
};
