forbid(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && ((if (action in action) then (if false then action else action) else (if false then action else action)) in (if (action in action) then action else action))) && false
};
