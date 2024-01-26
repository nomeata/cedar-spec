permit(
  principal,
  action == Action::"action",
  resource
) when {
  (true && (resource in resource)) && (a::"" in principal)
};
