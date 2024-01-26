permit(
  principal is a in a::"x",
  action in [],
  resource
) when {
  true && ((action == (principal.containsAny(principal))).containsAny(principal))
};
