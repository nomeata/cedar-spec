permit(
  principal == a::"",
  action in [],
  resource == a::""
) when {
  ((true && (principal && principal)) && principal) && principal
};
