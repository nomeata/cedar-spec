permit(
  principal == a::"",
  action,
  resource
) when {
  ((true && ((if false then [] else []).containsAny(if ((ip("107.110.0.5")).isInRange(ip("107.110.43.5"))) then [8085709789804770870] else []))) && true) && true
};
