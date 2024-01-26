permit(
  principal == a::"\0\0\0",
  action in [Action::"action"],
  resource in a::"\0\0\0"
) when {
  ((true && ([principal, principal, principal, principal, Ahhch::"", action, resource] == [principal, principal, principal, context, principal, principal, principal])) && principal) && principal
};
