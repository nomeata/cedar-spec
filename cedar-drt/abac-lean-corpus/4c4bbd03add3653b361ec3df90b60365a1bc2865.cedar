permit(
  principal,
  action == Action::"action",
  resource
) when {
  true && (!a::"\0\0")
};
