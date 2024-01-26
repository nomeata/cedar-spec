permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  false && action
};
