forbid(
  principal == a::"6",
  action in [Action::"action"],
  resource is a in a::"6"
) when {
  (true && ((if (action in action) then (if false then action else action) else (if false then action else action)) in (if (principal in action) then Action::"action" else (if false then action else action)))) && false
};
