permit(
  principal == a::"CCC",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && (action has "")
};
