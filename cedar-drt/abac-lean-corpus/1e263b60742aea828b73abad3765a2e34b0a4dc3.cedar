permit(
  principal == a::"p",
  action,
  resource
) when {
  ((true && context) && action) && resource
};
