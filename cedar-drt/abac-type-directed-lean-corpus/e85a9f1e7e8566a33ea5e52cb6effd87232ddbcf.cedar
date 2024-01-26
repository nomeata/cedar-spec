permit(
  principal == a::"6",
  action == Action::"action",
  resource is a
) when {
  true && ([false].containsAll([principal]))
};
