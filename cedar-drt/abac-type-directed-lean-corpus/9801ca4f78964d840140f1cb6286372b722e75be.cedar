permit(
  principal == a::"6666662\u{1}6666666666666666",
  action,
  resource in a::"6666662\u{1}6666666666666666"
) when {
  ((true && ((if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)) in (if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)))) && ((if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)) in (if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)))) && ((if true then resource else resource) in resource)
};
