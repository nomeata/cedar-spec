permit(
  principal,
  action,
  resource in a::""
) when {
  ((true && (true in ([principal, false].contains(Action::"action" == true)))) && action) && Action::"action"
};
