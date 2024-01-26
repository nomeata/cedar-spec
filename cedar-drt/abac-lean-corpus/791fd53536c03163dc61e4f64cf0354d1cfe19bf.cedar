forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && [resource, false]
};
