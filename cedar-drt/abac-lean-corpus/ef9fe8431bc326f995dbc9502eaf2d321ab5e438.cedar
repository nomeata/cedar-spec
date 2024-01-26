permit(
  principal is a in a::"j",
  action,
  resource == a::"j"
) when {
  true && ([Action::"action", Action::"action" in Action::"action"].containsAny([a::"", principal, a::"j", Action::"action", Action::"action" in a::"j", context, [a::"", a::"", a::"", Action::"action", false, resource, true]]))
};
