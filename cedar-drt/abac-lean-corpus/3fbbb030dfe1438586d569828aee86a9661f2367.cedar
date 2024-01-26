forbid(
  principal is a,
  action in [Action::"action"],
  resource == a::"jj"
) when {
  (true && (([a::"", true, a::"", Action::"action", context, resource].containsAll([true, action, a::"jj", context, a::"jj", a::"jj", a::""])) == a::"")) && principal
};
