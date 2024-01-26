forbid(
  principal == a::"jj",
  action in [Action::"action"],
  resource == a::"jj"
) when {
  (true && (([a::"", true, "", a::"", I0O00::"", Action::"action"].containsAll([Action::"action", context, principal])) == principal)) && principal
};
