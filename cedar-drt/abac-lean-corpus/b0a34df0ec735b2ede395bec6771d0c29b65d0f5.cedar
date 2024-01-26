permit(
  principal is a,
  action in [Action::"action"],
  resource
) when {
  (true && a::"\0\0\0") && resource
};
