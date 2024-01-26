forbid(
  principal,
  action,
  resource
) when {
  ((true && principal) && false) && false
};
