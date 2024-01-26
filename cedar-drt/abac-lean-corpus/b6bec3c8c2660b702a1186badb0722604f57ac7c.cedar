permit(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && ([principal, principal].isIpv4(principal, principal))) && principal) && principal
};
