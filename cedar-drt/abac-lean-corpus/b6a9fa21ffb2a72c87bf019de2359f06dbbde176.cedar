forbid(
  principal is a,
  action in [Action::"action"],
  resource
) when {
  true && (((Action::"action" == a::"") == (principal == A00::"")) == principal)
};
