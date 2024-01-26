forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  ((true && (![["", "", resource, "", "j", ""], [], ["", "", "", "", Action::"action", false], action, [false, principal, principal, principal, principal], principal])) && principal) && principal
};
