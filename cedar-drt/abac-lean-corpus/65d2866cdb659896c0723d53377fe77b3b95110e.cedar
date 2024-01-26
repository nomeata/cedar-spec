permit(
  principal,
  action,
  resource is a in a::""
) when {
  ((true && [context, a::"", principal, principal, principal, principal, principal]) && principal) && principal
};
