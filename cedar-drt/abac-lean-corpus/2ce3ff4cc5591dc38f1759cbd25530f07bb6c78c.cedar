permit(
  principal,
  action == Action::"action",
  resource == a::"ij"
) when {
  (true && ((a::"" == a::"ij").containsAll(principal))) && action
};
