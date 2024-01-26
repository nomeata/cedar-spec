forbid(
  principal is a in a::"\0",
  action in [Action::"action"],
  resource == a::"\0"
) when {
  (true && (((principal in context) in (Action::"action" in false)) in (["", principal, principal, principal, principal, principal, principal] == principal))) && principal
};
