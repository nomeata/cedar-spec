permit(
  principal in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::""
) when {
  ((true && ((if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)) in (if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)))) && ((if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)) in (if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)))) && ((if (resource in principal) then resource else resource) in resource)
};
