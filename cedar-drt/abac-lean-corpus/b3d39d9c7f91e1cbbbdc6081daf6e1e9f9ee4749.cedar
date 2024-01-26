@r("000")
forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (r::"" in principal)) && principal) && principal
};
