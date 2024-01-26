permit(
  principal is a,
  action in [Action::"policies"],
  resource == a::""
) when {
  true
};
