forbid(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && (if ((false == principal) == Action::"action") then a::"" else Action::"action")
};
