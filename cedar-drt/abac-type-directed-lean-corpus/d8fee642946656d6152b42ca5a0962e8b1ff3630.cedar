forbid(
  principal is a in a::"",
  action == Action::"action",
  resource == a::""
) when {
  (true && ([if false then [] else [], if false then [] else [], if true then [] else []].containsAny([[[], []], [], []]))) && false
};
