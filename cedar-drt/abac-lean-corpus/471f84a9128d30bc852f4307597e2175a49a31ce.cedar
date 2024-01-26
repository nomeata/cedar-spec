permit(
  principal is a in a::"j",
  action,
  resource == a::"j"
) when {
  true && ([Action::"action", Action::"action" in Action::"action"].containsAny([a::"", a::"", principal, context, a::"", a::"", a::""]))
};
