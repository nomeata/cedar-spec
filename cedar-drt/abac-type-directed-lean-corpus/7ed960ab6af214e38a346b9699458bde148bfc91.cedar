permit(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  true && (if (!(!true)) then ((if true then resource else resource) in (if true then resource else resource)) else true)
};
