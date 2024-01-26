@z("6")
permit(
  principal in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource is a in a::""
) when {
  ((true && ((action in action) || (action in action))) && (action in action)) && (action in action)
};
