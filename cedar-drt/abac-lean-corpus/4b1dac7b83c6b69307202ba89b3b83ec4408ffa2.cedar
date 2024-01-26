permit(
  principal in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && ((principal.lessThanOrEqual(principal)) == principal)
};
