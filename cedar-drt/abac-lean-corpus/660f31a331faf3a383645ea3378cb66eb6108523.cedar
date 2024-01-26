permit(
  principal == AhgAO::a::"\0\0",
  action in [AhgAO::Action::"action"],
  resource in AhgAO::a::"\0\0"
) when {
  ((true && ([AhgAO::a::"\0\0", principal, principal, principal, action, AhgAO::Action::"action", resource] == [action, wLHLN000Ovhjhhh::"", resource, [principal, resource, "", "", "", AhgAO::Action::"action", false], AhgAO::Action::"action", AhgAO::Action::"action", true])) && true) && false
};
