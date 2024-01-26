permit(
  principal is a,
  action in [Action::"action"],
  resource
) when {
  ((true && ((resource == resource) || (resource in resource))) && (resource in a::"\u{1}")) && false
};
