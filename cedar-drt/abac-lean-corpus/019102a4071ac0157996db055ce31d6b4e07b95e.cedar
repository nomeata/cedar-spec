permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (([false, Action::"action", Action::"action"].containsAll([E::"\0\0\0", a::"b??????jjj"])) == true)) && true
};
