permit(
  principal == a::"",
  action,
  resource == a::""
) when {
  true && ((ip(principal)) has "m")
};
