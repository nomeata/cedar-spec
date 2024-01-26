permit(
  principal is a,
  action == Action::"action",
  resource == a::""
) when {
  true && (principal.lessThan(resource))
};
