permit(
  principal == a::"\0\0\0",
  action in [Action::"action"],
  resource == a::"\0\0\0"
) when {
  ((true && (false.containsAll(principal))) && principal) && principal
};
