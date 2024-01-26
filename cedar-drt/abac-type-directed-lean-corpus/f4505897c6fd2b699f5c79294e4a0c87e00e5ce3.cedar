permit(
  principal == a::"",
  action in [Action::"action",Action::"action"],
  resource is a in a::""
) when {
  false
};
