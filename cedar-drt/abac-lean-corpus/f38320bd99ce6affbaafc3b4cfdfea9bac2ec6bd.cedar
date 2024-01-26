forbid(
  principal is hN in hN::"",
  action in [Action::"action"],
  resource is hN in hN::""
) when {
  (true && ([[false, Ah200::""], context][""])) && principal
};
