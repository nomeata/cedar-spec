permit(
  principal == a::"",
  action,
  resource
) when {
  true && (context has "o\0")
};
