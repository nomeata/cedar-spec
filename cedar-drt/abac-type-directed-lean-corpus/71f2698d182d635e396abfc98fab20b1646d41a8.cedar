permit(
  principal,
  action in [Action::"action",Action::"action"],
  resource is a in a::""
) when {
  ((true && ([[], []].contains([a::"", a::"", action]))) && false) && false
};
