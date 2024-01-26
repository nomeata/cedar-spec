forbid(
  principal in r::"",
  action == Action::"action",
  resource is r in r::""
) when {
  true
};
