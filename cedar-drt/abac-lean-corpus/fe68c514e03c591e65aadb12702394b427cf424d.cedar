permit(
  principal is a in a::"",
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  (true && [a::"", principal, principal, principal, principal]) && principal
};
