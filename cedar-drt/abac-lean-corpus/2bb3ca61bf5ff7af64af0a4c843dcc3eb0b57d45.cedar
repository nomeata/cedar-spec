permit(
  principal == a::"",
  action,
  resource == a::""
) when {
  (true && a::"") && a::""
};
