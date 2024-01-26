permit(
  principal == a::"",
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  (true && ((!Action::"action") == ([principal, principal, principal, principal, principal, principal, principal][""]))) && principal
};
