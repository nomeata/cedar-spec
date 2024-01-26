forbid(
  principal == a::"",
  action == Action::"action",
  resource is a in a::"\0\0"
) when {
  true && ((!false) || ([].containsAny([])))
};
