permit(
  principal is a,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && (action is a)) && (principal in resource)) && false
};
