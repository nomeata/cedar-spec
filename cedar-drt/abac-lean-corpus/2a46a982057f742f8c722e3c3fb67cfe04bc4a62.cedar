permit(
  principal,
  action in [Action::"action"],
  resource in a::"r"
) when {
  (true && (!action)) && false
};
