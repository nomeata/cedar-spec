permit(
  principal == a::"j",
  action in [Action::"action"],
  resource
) when {
  true && (principal in action)
};
