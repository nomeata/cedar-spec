permit(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  ((true && (["o\0\0\0\0\0"].containsAll([]))) && false) && false
};
