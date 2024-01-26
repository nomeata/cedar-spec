forbid(
  principal in a::"\0",
  action == Action::"action",
  resource in a::"\0"
) when {
  (true && ((if (resource has "m_qs") then (if false then resource else resource) else (if false then resource else resource)) has "m_qs")) && ((if (resource has "m_qs") then (if false then resource else resource) else (if false then resource else resource)) has "m_qs")
};
