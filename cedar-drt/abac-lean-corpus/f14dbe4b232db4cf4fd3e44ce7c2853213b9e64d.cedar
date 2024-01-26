permit(
  principal == a::"\0\0\0",
  action in [Action::"action"],
  resource in a::"\0\0\0"
) when {
  ((true && ([a::"\0\0\0", principal, principal, principal, action, Action::"action", resource] == [principal, principal, principal, principal, Ahhch::"", action, pN000O30::Ahhrc::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0"])) && principal) && false
};
