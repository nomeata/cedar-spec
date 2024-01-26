permit(
  principal == a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0",
  action,
  resource == a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0"
) when {
  true && (!action)
};
