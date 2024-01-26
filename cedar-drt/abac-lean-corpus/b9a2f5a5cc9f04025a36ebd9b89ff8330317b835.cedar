permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (([false, Action::"action", Action::"action"].containsAll([l::A::"", context])) == (a::"j" in (!principal)))) && principal
};
