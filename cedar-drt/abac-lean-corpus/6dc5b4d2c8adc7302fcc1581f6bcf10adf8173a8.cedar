permit(
  principal == a::"",
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  (true && ((!(Action::"action" is a)) is a)) && ((!(principal.containsAll(principal))) is a)
};
