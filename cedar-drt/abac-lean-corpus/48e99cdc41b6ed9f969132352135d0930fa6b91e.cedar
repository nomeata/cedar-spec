permit(
  principal == a::"",
  action,
  resource is a
) when {
  true && (context == principal)
};
