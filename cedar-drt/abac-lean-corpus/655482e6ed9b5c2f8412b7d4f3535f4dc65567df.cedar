permit(
  principal == a::"",
  action == Action::"action",
  resource is a
) when {
  ((true && (!(!(!principal)))) && resource) && principal
};
