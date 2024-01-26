permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (([false, Action::"action", true].containsAll([false, Action::"action", Action::"action"])) == [Action::"action", [false, principal, principal], principal, principal, principal, principal, principal])) && principal
};
