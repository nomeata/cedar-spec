permit(
  principal,
  action,
  resource
) when {
  ((true && (Action::"action" == false)) && false) && principal
};
