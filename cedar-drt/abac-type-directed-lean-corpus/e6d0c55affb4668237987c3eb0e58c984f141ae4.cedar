forbid(
  principal in a::"",
  action == Action::"action",
  resource is a in a::""
) when {
  true && (resource in Action::"action")
};
