permit(
  principal is g::a,
  action in [g::Action::"action"],
  resource == g::a::""
) when {
  true
};
