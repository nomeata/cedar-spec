permit(
  principal == a::"j",
  action,
  resource
) when {
  (true && action) && principal
};
