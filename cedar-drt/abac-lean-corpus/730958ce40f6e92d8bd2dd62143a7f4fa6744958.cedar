permit(
  principal is a,
  action in [Action::"action"],
  resource
) when {
  ((true && A000M::"") && (a::"\0" < principal)) && principal
};
