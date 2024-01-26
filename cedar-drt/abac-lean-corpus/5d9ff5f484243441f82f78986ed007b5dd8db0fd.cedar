permit(
  principal,
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && (((false has "mpa") == principal) == principal)
};
