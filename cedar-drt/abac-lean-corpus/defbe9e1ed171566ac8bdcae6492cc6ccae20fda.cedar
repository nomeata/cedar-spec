permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && (true <= principal)) && principal
};
