forbid(
  principal == a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0:666666666\0\0\0\0\0\0\03666",
  action in [Action::"action"],
  resource == a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0:666666666\0\0\0\0\0\0\03666"
) when {
  (true && ((if (action in action) then (if false then action else action) else (if false then action else action)) in (if (action in action) then (if false then action else action) else (if false then action else action)))) && ((if (action in action) then (if false then action else action) else (if false then action else action)) in (if (action in action) then (if false then action else action) else (if false then action else action)))
};
