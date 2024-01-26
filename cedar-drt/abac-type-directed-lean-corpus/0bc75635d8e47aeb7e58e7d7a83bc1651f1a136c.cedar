permit(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  true && (resource is a)
};
