forbid(
  principal,
  action,
  resource
) when {
  ((true && (a::"" in principal)) && principal) && principal
};
