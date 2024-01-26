permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && ([false, principal, principal].containsAll(principal))) && principal
};
