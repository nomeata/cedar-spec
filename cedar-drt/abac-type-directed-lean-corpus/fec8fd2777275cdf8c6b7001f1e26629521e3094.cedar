permit(
  principal == a::"\0\065\0",
  action in [Action::"action"],
  resource
) when {
  ((true && (if (action in action) then ([].containsAny([])) else ([].containsAny([])))) && ([].containsAny([]))) && ([].containsAny([[true]]))
};
