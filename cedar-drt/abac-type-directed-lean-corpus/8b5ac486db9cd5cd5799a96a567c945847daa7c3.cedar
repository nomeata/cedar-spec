permit(
  principal is a in a::"666",
  action in [Action::"action",Action::"action",Action::"action"],
  resource
) when {
  ((true && ((action has "") == true)) && true) && true
};
