permit(
  principal is a,
  action in [Action::"action"],
  resource
) when {
  (true && (if false then (!Action::"action") else (if (true == principal) then principal else principal))) && principal
};
