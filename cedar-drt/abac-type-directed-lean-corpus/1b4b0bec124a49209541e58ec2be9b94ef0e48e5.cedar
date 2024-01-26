permit(
  principal is a in a::"o\0\0\0\0",
  action in [Action::"action"],
  resource
) when {
  ((true && (([true].contains(false)) == (a::"o\0\0\0\0" is a))) && false) && false
};
