permit(
  principal is a in a::"&6",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && ((if (principal in principal) then resource else principal) in principal)
};
