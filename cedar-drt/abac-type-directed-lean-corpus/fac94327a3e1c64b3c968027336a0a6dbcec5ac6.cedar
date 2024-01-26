permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  ((true && ((([].contains([])) || true) || true)) && ((principal in resource) || false)) && false
};
