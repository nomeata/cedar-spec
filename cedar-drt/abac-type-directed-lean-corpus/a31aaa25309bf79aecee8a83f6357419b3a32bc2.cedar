@Bsseee("")
forbid(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && ((if (action in action) then (if false then action else action) else principal) in resource)) && (true == true)
};
