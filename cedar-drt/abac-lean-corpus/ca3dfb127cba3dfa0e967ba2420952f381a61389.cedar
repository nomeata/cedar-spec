permit(
  principal,
  action,
  resource is a in a::""
) when {
  ((true && Action::"action") && (principal - principal)) && principal
};
