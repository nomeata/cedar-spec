permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (([false, Action::"action", Action::"action"].containsAll([true, a::"", context])) == (!principal))) && ((a::"bjjj" == Action::"action") in principal)
};
