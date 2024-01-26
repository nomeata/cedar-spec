permit(
  principal is a,
  action == Action::"action",
  resource in a::""
) when {
  (true && (principal is a)) && (principal is a)
};
