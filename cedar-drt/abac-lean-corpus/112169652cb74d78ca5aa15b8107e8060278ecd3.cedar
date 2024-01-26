permit(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource in a::"."
) when {
  true && ((principal["Mlb0"]) == action)
};
