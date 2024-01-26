@r("")
@uaaat("")
permit(
  principal is a,
  action in [Action::"action"],
  resource
) when {
  ((true && principal) && true) && true
};
