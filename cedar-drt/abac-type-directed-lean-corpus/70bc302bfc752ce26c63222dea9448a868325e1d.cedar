permit(
  principal == a::"CCC",
  action in [Action::"action"],
  resource
) when {
  true && (action has "")
};
