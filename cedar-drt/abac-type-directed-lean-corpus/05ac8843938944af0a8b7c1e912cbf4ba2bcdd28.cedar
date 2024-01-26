permit(
  principal == a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && ([resource is a].containsAny([]))) && false
};
