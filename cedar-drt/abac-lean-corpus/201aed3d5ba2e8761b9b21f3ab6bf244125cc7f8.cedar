permit(
  principal == a::"",
  action,
  resource == a::"_ACg\0\0.\0\0\0\0\0\0\0\0"
) when {
  true && (!action)
};
