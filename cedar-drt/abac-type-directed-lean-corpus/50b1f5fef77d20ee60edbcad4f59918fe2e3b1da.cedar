permit(
  principal,
  action in [Action::"action"],
  resource in a::""
) when {
  ((true && ((if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)) in (if (action in resource) then a::"" else (if true then resource else resource)))) && ((if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)) in (if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)))) && ((if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)) in (if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)))
};
