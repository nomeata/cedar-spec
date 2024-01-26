permit(
  principal == a::"jj",
  action in [Action::"action",Action::"action",Action::"action"],
  resource
) when {
  ((true && (!true)) && false) && a::"jj"
};
