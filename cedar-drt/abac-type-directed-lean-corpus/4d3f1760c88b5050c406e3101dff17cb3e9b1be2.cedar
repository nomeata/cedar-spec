@L("")
@r("66666")
permit(
  principal,
  action == Action::"action",
  resource == a::"\0\0\0A666666"
) when {
  true && ((if (resource has "r") then (if false then (-3906309966399130058) else 0) else 0) == 0)
};
