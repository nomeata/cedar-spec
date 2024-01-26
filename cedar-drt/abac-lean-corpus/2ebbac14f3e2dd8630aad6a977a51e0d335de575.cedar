permit(
  principal is a in a::"j",
  action,
  resource == a::"j"
) when {
  true && ([a::"j", context].containsAny([true == false, a::"", action, a::"", Action::"action", Action::"action", resource in principal]))
};
