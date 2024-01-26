permit(
  principal in a::"",
  action in [Action::"Jn"],
  resource == a::""
) when {
  true && principal
};
