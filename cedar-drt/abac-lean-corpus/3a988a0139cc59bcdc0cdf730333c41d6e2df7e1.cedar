forbid(
  principal == a::"jj",
  action in [Action::"action"],
  resource == a::"jj"
) when {
  (true && (([false, Action::"action", Action::"action"] == [Action::"action", context, action]).containsAll(!action))) && false
};
