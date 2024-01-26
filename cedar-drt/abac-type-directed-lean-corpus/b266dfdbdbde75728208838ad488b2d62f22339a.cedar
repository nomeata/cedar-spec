permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && ({"": ip("")} has "6")
};
