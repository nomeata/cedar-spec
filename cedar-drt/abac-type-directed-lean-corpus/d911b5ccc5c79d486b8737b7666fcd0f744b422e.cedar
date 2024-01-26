permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (a::"" in [principal, principal, resource])) && false) && false
};
