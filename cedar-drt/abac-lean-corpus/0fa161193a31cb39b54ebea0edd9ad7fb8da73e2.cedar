permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  ((true && (a::"".containsAll(principal.containsAll(principal)))) && principal) && principal
};
