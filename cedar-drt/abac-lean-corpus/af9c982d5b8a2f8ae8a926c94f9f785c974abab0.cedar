permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && a::"") && false) && resource
};
