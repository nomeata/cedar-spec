permit(
  principal == a::"",
  action,
  resource
) when {
  ((true && ((if false then [] else []).containsAny(if ((ip("107.110.0.5")).isInRange(ip("107.110.0.5"))) then [] else []))) && true) && true
};
