@A("\0")
@r("")
permit(
  principal,
  action in [A::Action::"action"],
  resource
) when {
  true
};
