permit(
  principal,
  action,
  resource
) when {
  ((true && ([Action::"j", principal].containsAny(principal))) && principal) && principal
};
