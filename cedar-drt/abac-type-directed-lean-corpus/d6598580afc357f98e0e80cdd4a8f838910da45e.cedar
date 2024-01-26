forbid(
  principal == a::"\0",
  action == Action::"action",
  resource is a in a::"\0"
) when {
  true && ([].containsAny([]))
};
