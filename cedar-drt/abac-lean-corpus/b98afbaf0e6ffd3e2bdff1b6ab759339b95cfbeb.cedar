permit(
  principal,
  action == Action::"action",
  resource == a::"ij"
) when {
  (true && (((a::"ons".containsAll(action)) == false).containsAll(true))) && a::"ij"
};
