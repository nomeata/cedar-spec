permit(
  principal == a::"",
  action == Action::"action",
  resource is a
) when {
  true && ([false].containsAll([principal]))
};
