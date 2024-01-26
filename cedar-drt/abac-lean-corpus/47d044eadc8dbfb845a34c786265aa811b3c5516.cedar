@r("\0")
permit(
  principal,
  action == Action::"action",
  resource
) when {
  true
};
