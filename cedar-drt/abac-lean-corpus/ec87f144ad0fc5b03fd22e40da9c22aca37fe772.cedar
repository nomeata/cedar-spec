permit(
  principal == a::"r",
  action in [Action::"action"],
  resource
) when {
  ((true && (!(!(!Action::"action")))) && (!(!(!Action::"action")))) && (!(!principal))
};
