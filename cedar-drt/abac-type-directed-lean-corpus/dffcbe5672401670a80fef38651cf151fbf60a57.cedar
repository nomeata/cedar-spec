forbid(
  principal,
  action == Action::"action",
  resource
) when {
  (true && (!true)) && (!(principal in principal))
};
