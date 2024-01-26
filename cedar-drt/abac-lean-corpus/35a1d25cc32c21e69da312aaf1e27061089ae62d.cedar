permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && principal) && {"d": principal}) && principal
};
