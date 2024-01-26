forbid(
  principal is a in a::"6",
  action in [Action::"action"],
  resource is a in a::"6"
) when {
  (true && (Action::"action" in a::"6")) && (if (if (if false then false else false) then (if false then false else true) else (principal has "")) then (action has "") else true)
};
