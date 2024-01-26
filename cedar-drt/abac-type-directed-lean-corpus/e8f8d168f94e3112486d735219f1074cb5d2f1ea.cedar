permit(
  principal,
  action == Action::"action",
  resource
) when {
  (true && (resource in action)) && false
};
