permit(
  principal is a,
  action in [Action::"action"],
  resource
) when {
  (true && principal) && (if (if action then false else (if principal then principal else principal)) then principal else principal)
};
