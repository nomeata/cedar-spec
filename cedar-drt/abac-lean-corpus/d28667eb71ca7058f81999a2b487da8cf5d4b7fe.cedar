permit(
  principal == a::"",
  action,
  resource == a::""
) when {
  true && (context + false)
};
