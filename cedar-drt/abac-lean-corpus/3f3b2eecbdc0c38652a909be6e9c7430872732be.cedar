permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (([false, Action::"action", Action::"action"].containsAll([true, E::"\0", a::""])) == (!principal))) && a::"bjjj"
};
