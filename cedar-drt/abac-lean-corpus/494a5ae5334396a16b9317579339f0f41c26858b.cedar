permit(
  principal == a::"",
  action,
  resource
) when {
  true && a::".\0\0"
};
