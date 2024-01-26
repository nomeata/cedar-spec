forbid(
  principal == a::"666\u{1}\06\u{3}\0\0\0\0\0\0\0",
  action in [Action::"action"],
  resource == a::"666\u{1}\06\u{3}\0\0\0\0\0\0\0"
) when {
  (true && ((if (action in action) then (if false then action else action) else (if false then action else action)) in (if (action in action) then (if false then principal else principal) else action))) && (!true)
};
