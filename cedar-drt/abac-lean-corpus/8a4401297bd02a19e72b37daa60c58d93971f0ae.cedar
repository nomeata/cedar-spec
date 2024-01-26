permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && (((false in resource) in principal) || principal)) && principal
};
