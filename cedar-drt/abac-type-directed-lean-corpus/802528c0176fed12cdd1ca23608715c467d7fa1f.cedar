permit(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  ((true && (["\0\0\0", "\0\0", ""].containsAll([]))) && false) && false
};
