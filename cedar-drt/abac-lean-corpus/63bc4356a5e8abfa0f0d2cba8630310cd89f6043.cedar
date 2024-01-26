permit(
  principal == a::"esj",
  action in [Action::"action"],
  resource == a::"esj"
) when {
  true && Action::"action"
};
