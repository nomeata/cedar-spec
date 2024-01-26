permit(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource is a in a::""
) when {
  (true && ([[a::"", false], principal][""])) && principal
};
