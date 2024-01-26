permit(
  principal,
  action == Action::"action",
  resource
) when {
  true && ([].containsAny([[false, false]]))
};
