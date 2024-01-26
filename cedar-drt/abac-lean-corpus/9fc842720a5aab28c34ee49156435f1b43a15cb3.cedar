forbid(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  ((true && (((a::"".containsAny(principal)) * 0) * 0)) && principal) && principal
};
