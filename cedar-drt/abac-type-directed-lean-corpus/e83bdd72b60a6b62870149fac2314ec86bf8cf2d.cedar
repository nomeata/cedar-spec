forbid(
  principal == a::"\n\0",
  action in [Action::"action"],
  resource in a::""
) when {
  ((true && ((if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)) in (if (action in resource) then (if true then resource else resource) else (if true then resource else resource)))) && ((if (action in resource) then (if false then action else resource) else action) in (if (resource in resource) then resource else resource))) && true
};
