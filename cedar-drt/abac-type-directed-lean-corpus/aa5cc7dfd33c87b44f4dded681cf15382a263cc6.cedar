permit(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && ((if (principal has "C") then (if false then resource else resource) else (if false then resource else resource)) has "C")) && ((if (principal has "C") then principal else resource) has "C")
};
