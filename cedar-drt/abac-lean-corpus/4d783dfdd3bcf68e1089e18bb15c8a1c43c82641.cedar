permit(
  principal == a::"j",
  action in [Action::"action"],
  resource
) when {
  true && (action in false)
};
