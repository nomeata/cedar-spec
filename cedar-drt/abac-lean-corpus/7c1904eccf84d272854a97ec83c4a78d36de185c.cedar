permit(
  principal == a::"\0\0\0",
  action in [Action::"action"],
  resource in a::"\0\0\0"
) when {
  ((true && ([a::"\0\0\0", principal, principal, principal, action, Action::"action", resource] == [action, wLHLN000Ovhjhhh::"", resource, [principal, principal, resource, "", "", "", ""], "" == "", "", "" == false])) && principal) && principal
};
