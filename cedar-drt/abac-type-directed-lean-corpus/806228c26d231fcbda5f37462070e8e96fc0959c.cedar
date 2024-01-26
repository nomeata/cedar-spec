permit(
  principal in a::"333",
  action == Action::"action",
  resource in a::"333"
) when {
  (true && ((if (resource has "v") then (if false then resource else resource) else (if false then resource else resource)) has "v")) && ((if (resource has "v") then (if false then resource else resource) else resource) has "v")
};
