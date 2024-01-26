@A("\0]")
permit(
  principal,
  action == Action::"action",
  resource is a in a::"\0\0"
) when {
  true
};
