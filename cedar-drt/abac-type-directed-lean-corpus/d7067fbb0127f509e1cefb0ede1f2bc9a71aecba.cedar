permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && (action in action)) && (resource is a)) && true
};
