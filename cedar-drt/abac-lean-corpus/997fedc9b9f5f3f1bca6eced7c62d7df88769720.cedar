permit(
  principal == a::"jj",
  action in [Action::"nks-`"],
  resource is a in a::"jj"
) when {
  (true && [[action, a::"jj", At1j0::"i", false, false, principal].greaterThan(principal), principal, principal, principal, action, false.containsAll(action)]) && action
};
