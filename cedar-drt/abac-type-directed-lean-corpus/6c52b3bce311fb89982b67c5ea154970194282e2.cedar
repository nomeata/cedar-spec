permit(
  principal == a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::""
) when {
  ((true && ((if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)) in (if (resource in resource) then (if true then principal else principal) else action))) && (action in action)) && (resource in action)
};
