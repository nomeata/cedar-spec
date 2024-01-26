permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && Action::"action") && false) && action
};
