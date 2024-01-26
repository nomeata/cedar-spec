permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ([].contains(false))) && true) && false
};
