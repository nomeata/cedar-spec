forbid(
  principal == a::"jj",
  action in [Action::"action"],
  resource == a::"jj"
) when {
  (true && (([a::"", true, a::"", Action::"action", context, resource].containsAll([Action::"action", a::"jj", true, action, a::"jj", yp00000000000::"", principal])) == principal)) && principal
};
