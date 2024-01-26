permit(
  principal == a::"jte",
  action in [Action::"action"],
  resource == a::"jte"
) when {
  (true && (([false, a::"", Action::"action"].containsAll([l::A::"", Action::"action"])) == principal)) && principal
};
