permit(
  principal == a::"",
  action in [Action::""],
  resource == a::""
) when {
  false && principal
};
