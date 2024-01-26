forbid(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((a::"" == resource) || principal)
};
