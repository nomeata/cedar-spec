permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a
) when {
  true && [principal, principal, false, principal, resource]
};
