forbid(
  principal == a::"666",
  action in [Action::"action"],
  resource == a::"666"
) when {
  (true && ((if (action in action) then (if false then action else action) else (if false then action else action)) in (if (action in action) then (if false then action else action) else (if false then action else action)))) && (action in action)
};
