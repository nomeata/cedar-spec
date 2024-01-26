forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && ([[resource, action], if false then [] else []].containsAny([[[]]]))) && false
};
