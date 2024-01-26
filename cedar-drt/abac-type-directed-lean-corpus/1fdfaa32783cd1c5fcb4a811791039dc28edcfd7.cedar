permit(
  principal is a,
  action in [Action::"action"],
  resource is a in a::"666"
) when {
  true && (action has "")
};
