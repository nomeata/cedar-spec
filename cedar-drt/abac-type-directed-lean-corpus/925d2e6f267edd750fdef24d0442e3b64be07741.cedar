permit(
  principal == a::"",
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  (true && ((if (action in action) then (if false then action else action) else (if false then action else action)) in (if (action in action) then (if false then action else action) else (if false then action else principal)))) && (action in principal)
};
