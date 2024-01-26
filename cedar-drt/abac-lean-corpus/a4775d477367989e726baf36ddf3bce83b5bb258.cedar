permit(
  principal is a,
  action in [Action::"action"],
  resource == a::"bjjjj"
) when {
  (true && (!false)) && Action::"action"
};
