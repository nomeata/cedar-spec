permit(
  principal == a::"",
  action,
  resource
) when {
  true && (a::"7" in principal)
};
