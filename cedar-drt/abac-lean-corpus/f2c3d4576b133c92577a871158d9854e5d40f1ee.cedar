permit(
  principal,
  action == Action::"action",
  resource
) when {
  true && (!Action::"action")
};
