forbid(
  principal == a::"",
  action in [Action::""],
  resource == a::""
) when {
  (true && ((if (action in action) then (if false then action else action) else (if false then action else principal)) in resource)) && (true == true)
};
