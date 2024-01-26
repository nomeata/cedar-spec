forbid(
  principal in a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  true && ([].containsAll([resource in principal, resource in resource]))
};
