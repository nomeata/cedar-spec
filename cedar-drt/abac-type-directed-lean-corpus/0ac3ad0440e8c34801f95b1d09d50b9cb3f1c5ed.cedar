@F("n")
forbid(
  principal,
  action in [Action::"3"],
  resource
) when {
  ((true && ((if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)) == (if (resource in resource) then (if false then principal else resource) else (if true then resource else principal)))) && (p::"" is p)) && ((if (action in resource) then (if true then resource else resource) else (if true then resource else resource)) in (if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)))
};
