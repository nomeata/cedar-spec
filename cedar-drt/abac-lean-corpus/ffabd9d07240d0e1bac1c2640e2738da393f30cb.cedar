permit(
  principal == a::"jj&\0\0",
  action in [Action::"action"],
  resource
) when {
  (true && resource) && (!(!(!"")))
};
