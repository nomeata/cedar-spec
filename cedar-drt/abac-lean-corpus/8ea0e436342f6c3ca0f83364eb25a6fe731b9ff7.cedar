forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  true && (if (!principal) then principal else principal)
};
