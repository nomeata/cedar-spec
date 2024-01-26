permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  ((true && ([if false then [] else [], [false]].containsAny([]))) && false) && true
};
