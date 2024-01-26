permit(
  principal,
  action in [],
  resource
) when {
  ((true && principal) && (((action || Action::"action") || (false || a::"")) || principal)) && principal
};
