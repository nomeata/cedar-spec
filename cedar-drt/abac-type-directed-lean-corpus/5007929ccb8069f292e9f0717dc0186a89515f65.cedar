permit(
  principal in a::"\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::"\0"
) when {
  (true && ((if (resource has "C") then resource else resource) has "C")) && false
};
