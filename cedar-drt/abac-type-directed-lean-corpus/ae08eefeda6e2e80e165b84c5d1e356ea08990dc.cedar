permit(
  principal == a::"666",
  action in [Action::"action"],
  resource
) when {
  ((true && ((if false then [] else []).containsAny(if ((ip("107.110.0.5")).isInRange(ip("112.54.54.5"))) then (if false then [] else []) else (if false then [] else [])))) && (!([].containsAll([])))) && false
};
