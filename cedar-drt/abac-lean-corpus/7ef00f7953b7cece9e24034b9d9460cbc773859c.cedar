permit(
  principal,
  action,
  resource is a in a::""
) when {
  ((true && Action::"action") && ((!false) - principal)) && Action::"action"
};
