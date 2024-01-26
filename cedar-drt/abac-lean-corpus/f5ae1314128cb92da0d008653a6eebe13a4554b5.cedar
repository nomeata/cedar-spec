permit(
  principal == a::"",
  action,
  resource
) when {
  true && a::"\u{10}\0\0"
};
