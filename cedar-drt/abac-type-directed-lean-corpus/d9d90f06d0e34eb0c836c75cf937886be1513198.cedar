forbid(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ((if (action in action) then (if false then [] else []) else (if false then [] else [])).containsAll(if (action in action) then (if false then [] else []) else [action]))) && ((if (action in action) then [[]] else [[], [], []]).containsAll(if (action in action) then (if false then [] else []) else [principal, principal, principal]))) && true
};
