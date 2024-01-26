forbid(
  principal == a::"jj",
  action in [Action::"action"],
  resource == a::"jj"
) when {
  (true && (([a::"", true, a::"", Action::"action", context, resource].containsAll([Action::"action", context, action])) == (!5017166111381099776))) && Action::"action"
};
