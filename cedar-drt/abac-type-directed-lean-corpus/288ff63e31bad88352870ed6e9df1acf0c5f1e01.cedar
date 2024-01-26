permit(
  principal,
  action == Action::"action",
  resource
) when {
  (true && (resource in resource)) && (principal in principal)
};
