permit(
  principal,
  action,
  resource == a::"\0\0m"
) when {
  (true && action) && principal
};
