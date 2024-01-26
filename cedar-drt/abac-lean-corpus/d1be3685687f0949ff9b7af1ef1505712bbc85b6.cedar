permit(
  principal == a::"\0\0\0\0",
  action,
  resource
) when {
  (true && (ip(context))) && principal
};
