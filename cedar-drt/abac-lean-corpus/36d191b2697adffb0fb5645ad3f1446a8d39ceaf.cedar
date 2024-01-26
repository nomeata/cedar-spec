forbid(
  principal,
  action,
  resource
) when {
  ((true && principal) && false) && principal
};
