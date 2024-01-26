forbid(
  principal == a::"jj",
  action in [Action::"action"],
  resource == a::"jj"
) when {
  (true && (([a::"", true, a::"", Action::"action", principal, a::"jj"].containsAll([])) == action)) && Action::"action"
};
