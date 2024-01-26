permit(
  principal,
  action,
  resource == a::":so*"
) when {
  (true && ([principal, principal, principal].contains(principal))) && principal
};
