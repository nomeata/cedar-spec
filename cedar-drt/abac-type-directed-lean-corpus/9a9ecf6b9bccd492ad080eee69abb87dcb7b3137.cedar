forbid(
  principal is a in a::"\0",
  action in [Action::"action"],
  resource is a in a::"\0"
) when {
  true && ((if (action has "Bssq") then (if false then action else action) else action) has "Bssq")
};
