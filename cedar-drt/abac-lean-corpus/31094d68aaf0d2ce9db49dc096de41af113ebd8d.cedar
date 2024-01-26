permit(
  principal is a in a::"r",
  action in [Action::"action"],
  resource is a
) when {
  (true && (principal.containsAny(context))) && true
};
