@B("")
@r("")
permit(
  principal is B in B::"\u{1}\0\0",
  action in [Action::"action"],
  resource
) when {
  true
};
