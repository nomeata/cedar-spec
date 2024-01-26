forbid(
  principal == a::"jj",
  action in [Action::"action"],
  resource
) when {
  ((true && ([] in principal)) && principal) && principal
};
