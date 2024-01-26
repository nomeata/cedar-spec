permit(
  principal,
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  true && (if ((if a::"" then principal else principal) == principal) then principal else principal)
};
