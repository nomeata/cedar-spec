permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a
) when {
  ((true && [false, false]) && principal) && false
};
