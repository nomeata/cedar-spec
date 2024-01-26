permit(
  principal == a::"6",
  action == Action::"action",
  resource == a::"6"
) when {
  true && ([false, false].containsAll([]))
};
