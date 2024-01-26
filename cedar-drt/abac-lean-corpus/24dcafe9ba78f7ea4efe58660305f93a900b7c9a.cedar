permit(
  principal == a::"",
  action,
  resource
) when {
  true && (context has "on\0")
};
