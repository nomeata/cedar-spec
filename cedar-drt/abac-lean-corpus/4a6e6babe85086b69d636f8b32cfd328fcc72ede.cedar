permit(
  principal == a::"",
  action,
  resource == a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0"
) when {
  true && (!action)
};
